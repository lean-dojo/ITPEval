(*
  Statement-only formalization of PutnamBench artifact putnam_1977_b6:
  a finite subgroup whose translates by a fixed group element all have cube
  equal to the identity generates at most three times the square of its order
  distinct nonempty alternating products. This file contains no proof.
*)

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
   let alternating_product =
     \(mul:G->G->G) (identity:G) (a:G) (xs:G list).
       ITLIST (\x acc. mul (mul x a) acc) xs identity in
   !mul:G->G->G identity:G ginv:G->G H P:G->bool h:num a:G.
     is_group mul identity ginv /\
     is_subgroup mul identity ginv H /\
     FINITE H /\
     h = CARD H /\
     (!x:G.
        x IN H
        ==> mul (mul (mul x a) (mul x a)) (mul x a) = identity) /\
     P =
       {g:G |
          ?xs:G list.
            ~(xs = []) /\
            (!x:G. MEM x xs ==> x IN H) /\
            g = alternating_product mul identity a xs}
     ==> FINITE P /\ CARD P <= 3 * h EXP 2`;;
