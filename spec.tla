---- MODULE spec ----

\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache
EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC, tlcApalache

(*

    @typeAlias: PID = Int;
    @typeAlias: IID = Int;
    @typeAlias: VALUE = Int;
    @typeAlias: TIME = Int;

    @typeAlias: READ_TRANSACTION = [
        pid : PID,
        start : TIME,
        iid : IID
    ];

    @typeAlias: WRITE_TRANSACTION = [
        pid : PID,
        start : TIME,
        value : IID => VALUE,
        iids : Set(IID),
        primary : IID,
        prewritten : Set(IID)
    ];

*)

CONSTANTS
    \* @type: PID;
    p0,
    \* @type: PID;
    p1,
    \* @type: PID;
    p2

NullInt == 0

DATA_VALUES == 1..2
IIDS == 1..2
PIDS == {p0, p1, p2}
PIDSymmetry == Permutations(PIDS)
WRITES == {SetAsFun(S) : S \in SUBSET (IIDS \X DATA_VALUES)}
MAX_TIME == 8
TIME_RANGE == 1..MAX_TIME
KEYS == IIDS \X TIME_RANGE

VARIABLES
    \* @type: TIME;
    time,
    \* @type: (IID, TIME) => Int; Value
    data,
    \* @type: (IID, TIME) => IID; Points to IID of primary or 0 for Null
    lock,
    \* @type: (IID, TIME) => TIME; Points to time of data, or 0 for Null
    write,
    \* @type: Set(WRITE_TRANSACTION);
    write_transactions,
    \* @type: Set(READ_TRANSACTION);
    read_transactions

IsLockedFrom(iid, t) ==         \E k \in {iid} \X TIME_RANGE : t <= k[2] /\ lock[k] # NullInt
IsWritFrom(iid, t) ==           \E k \in {iid} \X TIME_RANGE : t <= k[2] /\ write[k] # NullInt
IsLockedInRange(iid, t0, t1) == \E k \in {iid} \X TIME_RANGE : t0 <= k[2] /\ k[2] <= t1 /\ lock[k] # NullInt
IsWritInRange(iid, t0, t1) ==   \E k \in {iid} \X TIME_RANGE : t0 <= k[2] /\ k[2] <= t1 /\ write[k] # NullInt

Init == 
    /\ time = 1
    /\ data = [k \in KEYS |-> NullInt]
    /\ lock = [k \in KEYS |-> NullInt]
    /\ write = [k \in KEYS |-> NullInt]
    /\ write_transactions = {}
    /\ read_transactions = {}

NewWriteTransaction(p) ==
    /\ UNCHANGED data
    /\ UNCHANGED lock
    /\ UNCHANGED write
    /\ \E f \in WRITES : 
        \E primary \in DOMAIN f:
            write_transactions' = write_transactions \cup {[
                pid |-> p,
                start |-> time,
                value |-> f,
                iids |-> DOMAIN f,
                primary |-> primary,
                prewritten |-> {}
            ]}

NewReadTransaction(p) ==
    /\ UNCHANGED data
    /\ UNCHANGED lock
    /\ UNCHANGED write
    /\ \E iid \in IIDS : 
        read_transactions' = read_transactions \cup {[
            pid |-> p,
            start |-> time,
            iid |-> iid
        ]}

Write(t) ==
    LET
    Prewrite(iid) ==
        IF IsWritFrom(iid, t.start) \/ IsLockedFrom(iid, 0)
        THEN 
            (*Abort*)
            /\ UNCHANGED data
            /\ UNCHANGED lock
            /\ UNCHANGED write
            /\ write_transactions' = write_transactions \ {t}
        ELSE
            (*Succeed*)
            /\ data' = [data EXCEPT ![iid, t.start] = t.value[iid]]
            /\ lock' = [lock EXCEPT ![iid, t.start] = t.primary]
            /\ UNCHANGED write
            /\ write_transactions' = (write_transactions \ {t}) \cup {[t EXCEPT !.prewritten = @ \cup {iid}]}

    Commit(iid) ==
        IF lock[iid, t.start] = NullInt
        THEN 
            (*Abort*)
            /\ UNCHANGED data
            /\ UNCHANGED lock
            /\ UNCHANGED write
            /\ write_transactions' = write_transactions \ {t}
        ELSE
            (*Succeed*)
            /\ UNCHANGED data
            /\ lock' = [lock EXCEPT ![iid, t.start] = NullInt]
            /\ write' = [write EXCEPT ![iid, time] = t.start]
            /\ write_transactions' = write_transactions \ {t}

    IN
    CASE 
    (*Try lock the primary*)
        t.primary \notin t.prewritten 
                                                    -> Prewrite(t.primary)
    []
    (*Try lock a non primary*)
        /\ t.primary \in t.prewritten
        /\ t.iids \ t.prewritten # {}
                                                    -> 
                                                    LET 
                                                    iid == CHOOSE iid \in (t.iids \ t.prewritten) : TRUE
                                                    IN
                                                    Prewrite(iid)
    []
    (*Try commit the primary*)
        \A iid \in t.iids : iid \in t.prewritten
                                                    -> Commit(t.primary)
    
Read(t) ==
    LET
    DoRead == 
        \* ... could do something with the latest write time in range(0, time), for verification purposes
        \* but I'll skip that as more interested in learning the algorithm than verifying it.
        /\ UNCHANGED data
        /\ UNCHANGED lock
        /\ UNCHANGED write
        /\ read_transactions' = read_transactions \ {t}
    RollBack == 
        /\ data' = [data EXCEPT ![t.iid, t.start] = NullInt]
        /\ lock' = [lock EXCEPT ![t.iid, t.start] = NullInt]
        /\ UNCHANGED write
        /\ UNCHANGED read_transactions
    RollForward(primaryIID) == 
        (*
        We must know the IID of the primary in order to locate the entry in the write column
        that commits the write. We take the time of that committing entry and use it to rollforward.
        *)
        LET 
            CommitTime == CHOOSE ct \in TIME_RANGE : write[primaryIID, ct] = t.start
        IN
        /\ UNCHANGED data
        /\ lock' = [lock EXCEPT ![t.iid, t.start] = NullInt]
        /\ write' = [write EXCEPT ![t.iid, CommitTime] = t.start]
        /\ UNCHANGED read_transactions
    DoNothing == 
        /\ UNCHANGED data
        /\ UNCHANGED lock
        /\ UNCHANGED write
        /\ UNCHANGED read_transactions
    IN
    CASE
    (*Actually read*)
        /\ ~IsLockedInRange(t.iid, 1, t.start)
        /\ IsWritInRange(t.iid, 1, t.start)
                                                    -> DoRead
    []
    (*
        Find a primary lock.
        Delete the lock and the data.
    *)
        /\ lock[t.iid, t.start] = t.iid 
                                                    -> RollBack
    []
    (*
        Find a non primary lock pointing to deleted primary lock.
        Delete the non primary lock and the data.
    *)
        /\ lock[t.iid, t.start] # NullInt
        /\ lock[t.iid, t.start] # t.iid
        /\ lock[lock[t.iid, t.start]] = NullInt
        /\ data[lock[t.iid, t.start]] = NullInt
                                                    -> RollBack
    []
    (*
        Find a non primary lock pointing to deleted primary lock.
        The primary row has data (so there must be a write pointing to the data)
        Replace the lock with a write pointing to the data, at the commit time.
    *)
        /\ lock[t.iid, t.start] # NullInt
        /\ lock[t.iid, t.start] # t.iid
        /\ lock[lock[t.iid, t.start]] = NullInt
        /\ data[lock[t.iid, t.start]] # NullInt
                                                    -> RollForward(lock[t.iid, t.start])

    [] OTHER -> DoNothing \* If find non primary lock pointing to a non-deleted primary lock, for example.

WriterCrash(p, t) == 
    /\ UNCHANGED data
    /\ UNCHANGED lock
    /\ UNCHANGED write
    /\ write_transactions' = write_transactions \ {t}
    /\ UNCHANGED read_transactions

NextTransition == 
    \E p \in PIDS : 
        \/
            /\ ~(\E t \in write_transactions : t.pid = p)
            /\ NewWriteTransaction(p)
            /\ UNCHANGED read_transactions
        \/
            /\ ~(\E t \in read_transactions : t.pid = p)
            /\ NewReadTransaction(p)
            /\ UNCHANGED write_transactions
        \/ \E t \in write_transactions :
            /\ t.pid = p
            /\ Write(t)
            /\ UNCHANGED read_transactions
        \/ \E t \in  read_transactions :
            /\ t.pid = p
            /\ Read(t)
            /\ UNCHANGED write_transactions
        \/ \E t \in write_transactions :
            /\ t.pid = p
            /\ WriterCrash(p, t)

Next == 
    \/ /\ time < MAX_TIME
       /\ time' = time + 1
       /\ NextTransition
    (*Loop back to allow TLC to exhaust the state space.*)
    \/ /\ time = MAX_TIME
       /\ time' = 1
       /\ data' = [k \in KEYS |-> NullInt]
       /\ lock' = [k \in KEYS |-> NullInt]
       /\ write' = [k \in KEYS |-> NullInt]
       /\ write_transactions' = {}
       /\ read_transactions' = {}

====