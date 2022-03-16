---- MODULE spec ----

\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache
EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC, tlcApalache

(*

@typeAlias: PID = Int; Process ID.
@typeAlias: IID = Int; Item ID.
@typeAlias: VALUE = Int; Item value.
@typeAlias: TIME = Int;

@typeAlias: WRITE_TRANSACTION = [
    pid : PID,
    start: TIME,
    value : IID => VALUE,
    iids : Set(IID),
    primary : IID,
    prewritten : Set(IID)
];

*)

NullInt == 0

DATA_VALUES == 1..3
IIDS == 1..3
PIDS == {p0, p1, p2}
PIDSymmetry == Permutations(PIDS)
WRITES == {SetAsFun(S) : S \in SUBSET (IIDS \X DATA_VALUES)}

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
    write_transactions

DatasForItem(iid)  == {x \in DOMAIN data  : x[1] = iid}
LocksForItem(iid)  == {x \in DOMAIN lock  : x[1] = iid}
WritesForItem(iid) == {x \in DOMAIN write : x[1] = iid}

IsLockedFrom(iid, t0) ==        \E x LocksForItem(iid)  : t0 <= x[2]
IsWritFrom(iid, t0) ==          \E x WritesForItem(iid) : t0 <= x[2]
IsLockedInRange(iid, t0, t1) == \E x LocksForItem(iid)  : t0 <= x[2] /\ x[2] <= t1
IsWritInRange(iid, t0, t1) ==   \E x WritesForItem(iid) : t0 <= x[2] /\ x[2] <= t1

Init == 
    time = 1,
    data = [x \in IIDS \X {0} |-> NullInt]
    lock = [x \in IIDS \X {0} |-> NullInt]
    write = [x \in IIDS \X {0} |-> NullInt]
    write_transactions = {}

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
            /\ UNCHANGED write,
            /\ write_transactions' = (write_transactions \ {t}) \cup {[t EXCEPT !.prewritten = @ \cup {iid}]},

    Commit(iid) ==
        IF ~lock[iid, t.start]
        THEN 
            (*Abort*)
            /\ UNCHANGED data
            /\ UNCHANGED lock
            /\ UNCHANGED write
            /\ write_transactions' = write_transactions \ {t}
        ELSE
            (*Succeed*)
            /\ UNCHANGED data,
            /\ lock' = [lock EXCEPT ![iid, t.start] = NullInt],
            /\ write' = [write EXCEPT ![iid, time] = t.start],
            /\ write_transactions' = write_transactions \ {t}

    IN
    CASE 
    (*Try lock the primary*)
        t.primary \notin t.prewritten 
                                                    -> Prewrite(t.primary)
    []
    (*Try lock a non primary*)
        /\ t.primary \in t.prewritten
        /\ \E iid \in t.iids : iid \notin t.prewritten
                                                    -> Prewrite(iid)
    []
    (*Try commit the primary*)
        \A iid \in t.iids : iid \in t.prewritten
                                                    -> Commit(primary)
    
(*
TODO:
    Is should change reads to come from a bank of running transactions with a start time instead of using 'time'.
    Then I should sanity check, typecheck and check some atomicity properties.
    Ensure use of nullint does not collide anywhere.
    Fix time merger (should merge @@ with new time to grow functions)

    Explain how the logic to finish all the write_transactions is moved from the write transaction and put entirely on the rollforward.
    typecheck ;)
*)

Read(iid) ==
    LET 
    DoNothing ==
        /\ UNCHANGED data
        /\ UNCHANGED lock
        /\ UNCHANGED write
        /\ UNCHANGED write_transactions
    DoRead == DoNothing
        \* ... could do something with the latest write time in range(0, time), for verification purposes
    Rollback == 
        /\ UNCHANGED data' = [data EXCEPT ![iid, time] = NullInt]
        /\ lock' = [lock EXCEPT ![iid, time] = NullInt]
        /\ UNCHANGED write
        /\ UNCHANGED write_transactions
    RollForward(primaryIID) == 
        LET 
            CommitTime == 
            LET
            CommitingWriteIndex == CHOOSE x \in {y \in WritesForItem(primaryIID) : write[y] = time}
            IN CommitingWriteIndex[2]
        IN
        /\ UNCHANGED data
        /\ lock' = [lock EXCEPT ![iid, time] = NullInt]
        /\ write' = [write EXCEPT ![iid, CommitTime] = time]
        /\ UNCHANGED write_transactions

    IN
    CASE
    (*Actually read*)
        /\ ~IsLockedInRange(iid, 0, time)
        /\ IsWritInRange(iid, 0, time)
                                                    -> DoRead
    []
    (*
        Find a primary lock.
        Delete the lock and the data.
    *)
        /\ lock[iid, time] = iid 
                                                    -> RollBack
    []
    (*
        Find a lock with a missing primary. The primary item has no data.
        Delete the lock and the data.
    *)
        /\ lock[iid, time] # NullInt
        /\ lock[iid, time] # iid
        /\ lock[lock[iid, time]] = Nullint
        /\ data[lock[iid, time]] = NullInt
                                                    -> RollBack
    []
    (*
        Find a lock with a missing primary. The primary item has data (then there is a write pointing to the data)
        Replace the lock with a write pointing to the data, at the commit time.
    *)
        /\ lock[iid, time] # NullInt
        /\ lock[iid, time] # iid
        /\ lock[lock[iid, time]] = Nullint
        /\ data[lock[iid, time]] # NullInt
                                                    -> RollForward(lock[iid, time])

    [] OTHER -> DoNothing \* If find lock with a primary, for example.

NewWriteTransaction(p) ==
    /\ UNCHANGED data
    /\ UNCHANGED lock
    /\ UNCHANGED write
    /\ \E f \in WRITES : 
        write_transactions' = write_transactions \cup {[
            pid |-> p,
            start|-> time,
            value |-> f,
            iids |-> DOMAIN f,
            primary |-> CHOOSE id \in DOMAIN f,
            prewritten |-> {}
        ]}

WriterCrash(p, t) == 
    /\ UNCHANGED data
    /\ UNCHANGED lock
    /\ UNCHANGED write
    /\ write_transactions' = write_transactions \ {t}

Next == 
    /\ time' = time + 1
    /\ 
        \/ \E p \in PIDS : 
           \/ \E t \in write_transactions :
               /\ t.pid = p
               /\ Write(t)
           \/
               /\ ~(\E t \in write_transactions : t.pid = p)
               /\ NewWriteTransaction(p)
           \/ \E t \in write_transactions :
               /\ t.pid = p
               /\ WriterCrash(p, t)
        \/ \E iid \in IIDS: Read(iid)
    
Inv == Agreement

====