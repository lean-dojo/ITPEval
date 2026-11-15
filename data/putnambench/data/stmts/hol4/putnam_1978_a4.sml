(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a4:
  consequences of the bypass law (ab)(cd) = ad for a binary operation, and
  existence of a finite example with specified idempotence and nontriviality.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val putnam_1978_a4 =
  ``(!(mul : 'a -> 'a -> 'a).
       (!a b c d : 'a. mul (mul a b) (mul c d) = mul a d)
       ==>
       (!a b c : 'a.
          mul a b = c
          ==>
          mul c c = c /\ (!d : 'a. mul a d = mul c d))) /\
    (?S : num set.
       ?(mul : num -> num -> num).
         FINITE S /\
         (!a b : num. a IN S /\ b IN S ==> mul a b IN S) /\
         (!a b c d : num.
            a IN S /\ b IN S /\ c IN S /\ d IN S
            ==>
            mul (mul a b) (mul c d) = mul a d) /\
         (!a : num. a IN S ==> mul a a = a) /\
         (?a b : num.
            a IN S /\ b IN S /\ mul a b = a /\ a <> b) /\
         (?a b : num.
            a IN S /\ b IN S /\ mul a b <> a))``;
