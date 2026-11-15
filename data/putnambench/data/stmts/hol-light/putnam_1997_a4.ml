(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1997_a4:
  a triple-product invariance condition on a self-map of an arbitrary group
  implies that a left translate of the map is a homomorphism. This file
  contains no proof.
*)

let statement =
  `let is_group =
     \(mul:G->G->G) (identity:G) (ginv:G->G).
       (!x y z:G. mul (mul x y) z = mul x (mul y z)) /\
       (!x:G. mul identity x = x /\ mul x identity = x) /\
       (!x:G.
          mul (ginv x) x = identity /\ mul x (ginv x) = identity) in
   !mul:G->G->G identity:G ginv:G->G phi:G->G.
     is_group mul identity ginv /\
     (!g1 g2 g3 h1 h2 h3:G.
        mul (mul g1 g2) g3 = identity /\
        mul (mul h1 h2) h3 = identity
        ==> mul (mul (phi g1) (phi g2)) (phi g3) =
            mul (mul (phi h1) (phi h2)) (phi h3))
     ==> ?a:G.
           !x y:G.
             mul a (phi (mul x y)) =
             mul (mul a (phi x)) (mul a (phi y))`;;
