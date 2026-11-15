(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a5:
  no finite abelian group has product of all element orders equal to 2^2009.
  This file contains no proof.
*)

let statement =
  `let is_commutative_group =
     \(mul:G->G->G) (identity:G) (ginv:G->G).
       (!x y z:G. mul (mul x y) z = mul x (mul y z)) /\
       (!x:G. mul identity x = x /\ mul x identity = x) /\
       (!x:G.
          mul (ginv x) x = identity /\ mul x (ginv x) = identity) /\
       (!x y:G. mul x y = mul y x) in
   let is_power =
     \(mul:G->G->G) (identity:G) (x:G) (n:num) (y:G).
       ?powers:num->G.
         powers 0 = identity /\
         (!k:num. powers (SUC k) = mul x (powers k)) /\
         powers n = y in
   let is_order =
     \(mul:G->G->G) (identity:G) (x:G) (n:num).
       0 < n /\
       is_power mul identity x n identity /\
       (!m:num.
          0 < m /\ is_power mul identity x m identity
          ==> n <= m) in
   ~(?mul:G->G->G identity:G ginv:G->G ord:G->num.
       FINITE (UNIV:G->bool) /\
       is_commutative_group mul identity ginv /\
       (!g:G. is_order mul identity g (ord g)) /\
       nproduct (UNIV:G->bool) ord = 2 EXP 2009)`;;
