(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b3:
  group relations involving an element of order dividing three and an
  odd-power relation force the second element to be the identity. This file
  contains no proof.
*)

let statement =
  `let is_group =
     \(mul:G->G->G) (identity:G) (ginv:G->G).
       (!x y z:G. mul (mul x y) z = mul x (mul y z)) /\
       (!x:G. mul identity x = x /\ mul x identity = x) /\
       (!x:G.
          mul (ginv x) x = identity /\ mul x (ginv x) = identity) in
   let is_power =
     \(mul:G->G->G) (identity:G) (x:G) (n:num) (y:G).
       ?powers:num->G.
         powers 0 = identity /\
         (!k:num. powers (SUC k) = mul x (powers k)) /\
         powers n = y in
   !mul:G->G->G identity:G ginv:G->G A B:G.
     is_group mul identity ginv /\
     mul (mul A B) A = mul (mul B (mul A A)) B /\
     mul (mul A A) A = identity /\
     (?n:num. 0 < n /\ is_power mul identity B (2 * n - 1) identity)
     ==> B = identity`;;
