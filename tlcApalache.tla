
---- MODULE tlcApalache ---- 

EXTENDS Integers, FiniteSets, Sequences

(*****************************************************************************)
(* The folding operator, used to implement computation over a set.           *)
(* Apalache implements a more efficient encoding than the one below.         *)
(* (from the community modules).                                             *)
(*****************************************************************************)
RECURSIVE FoldSet(_,_,_)
FoldSet( Op(_,_), v, S ) == IF S = {}
                            THEN v
                            ELSE LET w == CHOOSE x \in S: TRUE
                                  IN LET T == S \ {w}
                                      IN FoldSet( Op, Op(v,w), T )

(*****************************************************************************)
(* The folding operator, used to implement computation over a sequence.      *)
(* Apalache implements a more efficient encoding than the one below.         *)
(* (from the community modules).                                             *)
(*****************************************************************************)
RECURSIVE FoldSeq(_,_,_)
FoldSeq( Op(_,_), v, seq ) == IF seq = <<>>
                              THEN v
                              ELSE FoldSeq( Op, Op(v,Head(seq)), Tail(seq) )

(*****************************************************************************)
(* Convert a set of pairs to a function.                                     *)
(* Apalache implements a more efficient encoding than the one below.         *)
(*****************************************************************************)
SetAsFun(S) ==
    LET Dom == { x: <<x, y>> \in S }
        Rng == { y: <<x, y>> \in S }
    IN
    [ x \in Dom |-> CHOOSE y \in Rng: <<x, y>> \in S ]
====
