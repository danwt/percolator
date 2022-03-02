---- MODULE spec ----

\* EXTENDS  Integers, FiniteSets, Sequences, TLC, Apalache
EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC

(*

@typeAlias: PID = Int;

*)

(*
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

NullInt == 0
NullStr == "NullStr"

VARIABLES
(*Meta*)
    \* @type: Str;
    action

Init == 
    /\ action = "init"

Next == TRUE

Inv == Agreement

====