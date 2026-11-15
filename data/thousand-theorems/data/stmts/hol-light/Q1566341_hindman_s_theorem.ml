(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1566341,
  "Hindman's theorem": in every finite cover of the finite-products set of an
  infinite sequence in a semigroup, one member contains the finite-products
  set of another infinite sequence. This file contains no proof.
*)

let Q1566341_HINDMAN_S_THEOREM =
  `let finite_products =
     \(op:A->A->A) (a:num->A).
       {x:A |
          ?indices:num list.
            ~(indices = []) /\
            PAIRWISE (\i j:num. i < j) indices /\
            x =
            ITLIST op (MAP a (BUTLAST indices)) (a (LAST indices))} in
   !op:A->A->A. !a:num->A. !s:(A->bool)->bool.
     (!x y z:A. op (op x y) z = op x (op y z)) /\
     FINITE s /\
     finite_products op a SUBSET UNIONS s
     ==> ?c:A->bool.
           c IN s /\
           ?b:num->A. finite_products op b SUBSET c`;;
