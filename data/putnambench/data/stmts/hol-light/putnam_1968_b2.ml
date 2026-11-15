(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b2:
  every element of a finite group is a product of two elements of any subset
  containing more than half the group. This file contains no proof.
*)

let statement =
  `let is_group =
     \(mul:G->G->G) (identity:G) (ginv:G->G).
       (!x y z:G. mul (mul x y) z = mul x (mul y z)) /\
       (!x:G. mul identity x = x /\ mul x identity = x) /\
       (!x:G.
          mul (ginv x) x = identity /\ mul x (ginv x) = identity) in
   !mul:G->G->G identity:G ginv:G->G A:G->bool.
     FINITE (UNIV:G->bool) /\
     is_group mul identity ginv /\
     CARD (UNIV:G->bool) DIV 2 < CARD A
     ==> !g:G. ?x y:G. x IN A /\ y IN A /\ g = mul x y`;;
