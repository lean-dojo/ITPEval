(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_a1:
  a binary operation satisfying (a * b) * a = b also satisfies
  a * (b * a) = b. This file contains no proof.
*)

let statement =
  `!op:'a->'a->'a.
     (!a b:'a. op (op a b) a = b)
     ==> (!a b:'a. op a (op b a) = b)`;;
