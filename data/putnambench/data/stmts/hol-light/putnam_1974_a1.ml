(*
  Statement-only formalization of PutnamBench artifact putnam_1974_a1:
  the maximum size, namely 11, of a subset of the integers from 1 through 16
  containing no three distinct pairwise coprime elements. This file contains
  no proof.
*)

let statement =
  `let conspiratorial =
     \S:int->bool.
       !a b c:int.
         a IN S /\ b IN S /\ c IN S /\
         ~(a = b) /\ ~(b = c) /\ ~(a = c)
         ==> ~coprime(a,b) \/ ~coprime(b,c) \/ ~coprime(a,c) in
   (?S:int->bool.
      FINITE S /\
      S SUBSET {x:int | &1 <= x /\ x <= &16} /\
      conspiratorial S /\
      CARD S = 11) /\
   (!S:int->bool.
      FINITE S /\
      S SUBSET {x:int | &1 <= x /\ x <= &16} /\
      conspiratorial S
      ==> CARD S <= 11)`;;
