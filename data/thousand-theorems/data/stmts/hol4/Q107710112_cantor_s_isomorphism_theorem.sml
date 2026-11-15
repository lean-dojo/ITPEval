(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q107710112, "Cantor's isomorphism theorem": any two countable, dense,
  nonempty linear orders without endpoints are order isomorphic. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q107710112_strict_order_def = new_definition (
  "q107710112_strict_order_def",
  ``q107710112_strict_order (leq : 'a -> 'a -> bool) x y <=>
      leq x y /\ x <> y``);

val q107710112_linear_order_def = new_definition (
  "q107710112_linear_order_def",
  ``q107710112_linear_order (leq : 'a -> 'a -> bool) <=>
      (!x. leq x x) /\
      (!x y. leq x y /\ leq y x ==> x = y) /\
      (!x y z. leq x y /\ leq y z ==> leq x z) /\
      (!x y. leq x y \/ leq y x)``);

val q107710112_dense_order_def = new_definition (
  "q107710112_dense_order_def",
  ``q107710112_dense_order (leq : 'a -> 'a -> bool) <=>
      !x y.
        q107710112_strict_order leq x y
        ==>
        ?z.
          q107710112_strict_order leq x z /\
          q107710112_strict_order leq z y``);

val q107710112_no_endpoints_def = new_definition (
  "q107710112_no_endpoints_def",
  ``q107710112_no_endpoints (leq : 'a -> 'a -> bool) <=>
      (!x. ?y. q107710112_strict_order leq y x) /\
      (!x. ?y. q107710112_strict_order leq x y)``);

val iso_of_countable_dense =
  ``!(leA : 'a -> 'a -> bool) (leB : 'b -> 'b -> bool).
      q107710112_linear_order leA /\
      q107710112_dense_order leA /\
      q107710112_no_endpoints leA /\
      (?encodeA : 'a -> num.
         INJ encodeA (UNIV : 'a set) (UNIV : num set)) /\
      q107710112_linear_order leB /\
      q107710112_dense_order leB /\
      q107710112_no_endpoints leB /\
      (?encodeB : 'b -> num.
         INJ encodeB (UNIV : 'b set) (UNIV : num set))
      ==>
      ?iso : 'a -> 'b.
        BIJ iso (UNIV : 'a set) (UNIV : 'b set) /\
        !(x : 'a) (y : 'a).
          (leA x y <=> leB (iso x) (iso y))``;
