(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a5:
  signed alternating representations of every element of a finite group
  generated jointly by two elements, but by neither alone, when the first
  generator has odd order. This file contains no proof.
*)

needs "Library/iter.ml";;

let statement =
  `let is_group =
     \(mul:G->G->G) (identity:G) (ginv:G->G).
       (!x y z:G. mul (mul x y) z = mul x (mul y z)) /\
       (!x:G. mul identity x = x /\ mul x identity = x) /\
       (!x:G.
          mul (ginv x) x = identity /\ mul x (ginv x) = identity) in
   let is_subgroup =
     \(mul:G->G->G) (identity:G) (ginv:G->G) (H:G->bool).
       identity IN H /\
       (!x:G. x IN H ==> ginv x IN H) /\
       (!x y:G. x IN H /\ y IN H ==> mul x y IN H) in
   let generated_by =
     \(mul:G->G->G) (identity:G) (ginv:G->G) (S:G->bool).
       !H:G->bool.
         is_subgroup mul identity ginv H /\ S SUBSET H
         ==> H = (UNIV:G->bool) in
   let has_order =
     \(mul:G->G->G) (identity:G) (x:G) (n:num).
       0 < n /\
       ITER n (mul x) identity = identity /\
       (!m:num.
          0 < m /\ ITER m (mul x) identity = identity
          ==> n <= m) in
   !mul:G->G->G identity:G ginv:G->G g h:G.
     FINITE (UNIV:G->bool) /\
     is_group mul identity ginv /\
     generated_by mul identity ginv {g,h} /\
     ~(generated_by mul identity ginv {g}) /\
     ~(generated_by mul identity ginv {h}) /\
     (?n:num. has_order mul identity g n /\ ODD n)
     ==>
     !x:G.
       ?mn:G list.
         1 <= LENGTH mn /\
         LENGTH mn <= CARD (UNIV:G->bool) /\
         (!z:G.
            MEM z mn
            ==> z IN
                {mul g h,
                 mul (ginv g) h,
                 mul g (ginv h),
                 mul (ginv g) (ginv h)}) /\
         x = ITLIST mul mn identity`;;
