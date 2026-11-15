(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a4:
  consequences of the bypass law (ab)(cd) = ad for a binary operation, and
  existence of a finite example with specified idempotence and nontriviality.
  This file contains no proof.
*)

let statement =
  `(!op:'a->'a->'a.
      (!a b c d:'a. op (op a b) (op c d) = op a d)
      ==>
      (!a b c:'a.
         op a b = c
         ==>
         op c c = c /\ (!d:'a. op a d = op c d))) /\
   (?S:num->bool.
      ?op:num->num->num.
        FINITE S /\
        (!a b:num. a IN S /\ b IN S ==> op a b IN S) /\
        (!a b c d:num.
           a IN S /\ b IN S /\ c IN S /\ d IN S
           ==>
           op (op a b) (op c d) = op a d) /\
        (!a:num. a IN S ==> op a a = a) /\
        (?a b:num.
           a IN S /\ b IN S /\ op a b = a /\ ~(a = b)) /\
        (?a b:num.
           a IN S /\ b IN S /\ ~(op a b = a)))`;;
