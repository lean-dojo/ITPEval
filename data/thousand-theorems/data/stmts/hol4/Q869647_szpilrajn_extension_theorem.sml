(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q869647, "Szpilrajn extension theorem": every partial order on an arbitrary,
  possibly empty carrier extends to a linear order. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val q869647_partial_order_on_def = new_definition (
  "q869647_partial_order_on_def",
  ``q869647_partial_order_on
      (carrier : 'a -> bool) (r : 'a -> 'a -> bool) <=>
      (!x. carrier x ==> r x x) /\
      (!x y z.
        carrier x /\ carrier y /\ carrier z /\ r x y /\ r y z
        ==>
        r x z) /\
      (!x y.
        carrier x /\ carrier y /\ r x y /\ r y x
        ==>
        x = y)``);

val q869647_linear_order_on_def = new_definition (
  "q869647_linear_order_on_def",
  ``q869647_linear_order_on
      (carrier : 'a -> bool) (r : 'a -> 'a -> bool) <=>
      q869647_partial_order_on carrier r /\
      (!x y.
        carrier x /\ carrier y
        ==>
        r x y \/ r y x)``);

val extend_partialOrder =
  ``!(carrier : 'a -> bool) (r : 'a -> 'a -> bool).
      q869647_partial_order_on carrier r
      ==>
      ?s : 'a -> 'a -> bool.
        q869647_linear_order_on carrier s /\
        !x y.
          carrier x /\ carrier y /\ r x y
          ==>
          s x y``;
