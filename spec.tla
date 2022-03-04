---- MODULE spec ----

\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache
EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC, tlcApalache

(*
cross-row, cross-table transac- tions with ACID snapshot-isolation semantics

TODO: the data should probably be a 3 index'd tuple -> value map
where the key is (ADDR, TIMESTAMP, TYPE) and TYPE is data/lock/write

Processes need to interleave so some meta state might be needed to prompt their forward progress
(or lack of it).

To recall:
    writers get start_timestamp and make successive row transactions
     to write data X lock. The first row is the primary. They abort if
     any lock is encountered across all timestamps or if any write is 
     encountered in a timestamp t, start_timestamp < t.
     Once all cells are locked, each lock is swapped for a write, starting
     with the primary.
     TODO: CHECK LINE 53 of PAPER PSUEDOCODE - It doesn't seem necessary or useful to me?
     Also, the pseudocode erases the lock with timestamp commit_Ts which seems like a mistake
         I think it should erase at start_ts
    
    Each lock is primary or points to the pimary. Each write points to its data cell. 
    Get operations check for a lock in [0, start_timestamp] and maybe try to cleanup
    if there is one. Writes that aborted before they wrote the primary write will have a primary
    lock. Cleaners can atomically remove the primary lock to cleanup. If a cleaner finds
        a lock which is a pointer to a missing primary lock, it can delete the lock. If a cleaner
        finds a lock which is a pointer to a _write_ then the cleaner cannot cleanup but should
        swap the remaining locks for writes as necessary to complete the transaction.
        
*)

(*

@typeAlias: PID = Int; Process ID.
@typeAlias: IID = Int; Item ID.
@typeAlias: VALUE = Int; Item value.
@typeAlias: TIME = Int;

@typeAlias: WRITE_TRANSACTION = [
    pid : PID,
    start: TIME,
    commit : TIME,
    value : IID => VALUE,
    iids : Set(IID),
    primary : IID,
    prewritten : Set(IID),
    postwritten : Set(IID)
];

*)


NullInt == 0
NullStr == "NullStr"

IIDS == 1..3
PIDS == {p0,p1,p2}
PIDSymmetry == Permutations(PIDS)
VALUES == 0..2
WRITES == {SetAsFun(S) : S \in SUBSET IIDS \X VALUES}

VARIABLES
    \* @type: TIME;
    time,
    \* @type: (IID, TIME) => Int;
    data,
    \* @type: (IID, TIME) => Int;
    lock,
    \* @type: (IID, TIME) => Int;
    write,
    \* @type: Set(WRITE_TRANSACTION);
    writes,
    \* @type: Set(READ_TRANSACTION);
    reads

IsLockedFrom(iid, t0) ==        \E pair \in DOMAIN lock  : pair[1] = iid /\ t0 <= pair[2]
IsWritedFrom(iid, t0) ==        \E pair \in DOMAIN write : pair[1] = iid /\ t0 <= pair[2]
IsLockedInRange(iid, t0, t1) == \E pair \in DOMAIN lock  : pair[1] = iid /\ t0 <= pair[2] /\ pair[2] <= t1
IsWritedInRange(iid, t0, t1) == \E pair \in DOMAIN write : pair[1] = iid /\ t0 <= pair[2] /\ pair[2] <= t1

Init == 
    /\ action = "init"

Write(t) ==
    LET
    Prewrite(iid) ==
        IF IsWritedFrom(iid, t.start) \/ IsLockedFrom(iid, 0)
            (*Abort*)
        THEN 
            /\ UNCHANGED data,
            /\ UNCHANGED lock,
            /\ UNCHANGED write,
            /\ writes' = writes \ {t}
            /\ UNCHANGED reads
        ELSE
        /\ data' = [data EXCEPT ![iid, t.start] = t.value[iid]]
        /\ lock' = [lock EXCEPT ![iid, t.start] = t.primary]
        /\ UNCHANGED write,
        /\ writes' = (writes \ {t}) \cup {[
                pid |-> t.pid,
                start|-> t.start,
                commit |-> t.commit,
                value |-> t.value,
                iids |-> t.iids,
                primary |-> t.primary,
                prewritten |-> t.prewritten \cup {iid},
                postwritten |-> t.postwritten
            ]},
        /\ UNCHANGED reads


    IN
    CASE 
    (*Try lock the primary*)
        t.primary \notin t.prewritten 
                                                    -> Prewrite(t.primary)
    []
    (*Try lock a non primary*)
        \E iid \in t.iids : 
            /\ t.primary \notin t.prewritten
            /\ iid \notin t.prewritten
                                                    -> Prewrite(iid)
    []
    (*Commit the primary*)
        /\ \A iid \in t.iids : iid \in t.prewritten
        /\ lock[t.primary, t.start]
                                                    -> Commit(primary)

    []
    (*Abort*)
        /\ \A iid \in t.iids : iid \in t.prewritten
        /\ ~lock[t.primary, t.start]
                                                    -> Abort

    

Read(t) ==

NewWriteTransaction(p) ==
    /\ UNCHANGED data
    /\ UNCHANGED lock
    /\ UNCHANGED write
    /\ \E f \in WRITES : 
        writes' = writes \cup {[
            pid |-> p,
            start|-> time,
            commit |-> NullInt,
            value |-> f,
            iids |-> DOMAIN f,
            primary |-> CHOOSE id \in DOMAIN f,
            prewritten |-> {},
            postwritten |-> {}
        ]}
    /\ UNCHANGED reads

NewReadTransaction(p) ==
    /\ UNCHANGED data
    /\ UNCHANGED lock
    /\ UNCHANGED write
    /\ UNCHANGED writes
    /\ UNCHANGED reads


Next == 
    \E p \in PIDS : 
     /\ time' = time + 1
     /\ \/ \E t \in writes :
            /\ t.pid = p
            /\ Write(t)
        \/ \E t \in reads :
            /\ t.pid = p
            /\ Read(t)
        \/
            /\ ~(\E t \in writes : t.pid = p)
            /\ NewWriteTransaction(p)
        \/
            /\ ~(\E t \in reads : t.pid = p)
            /\ NewReadTransaction(p)

    
Inv == Agreement

====