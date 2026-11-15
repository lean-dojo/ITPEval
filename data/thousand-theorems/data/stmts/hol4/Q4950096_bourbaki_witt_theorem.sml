(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q4950096, "Bourbaki–Witt theorem": every inflationary endomap of a nonempty
  chain-complete partial order has a fixed point. This file contains no proof.
*)

open HolKernel Parse boolLib;

val q4950096_partial_order_def = new_definition (
  "q4950096_partial_order_def",
  ``q4950096_partial_order (leR : 'a -> 'a -> bool) <=>
      (!x. leR x x) /\
      (!x y z. leR x y /\ leR y z ==> leR x z) /\
      (!x y. leR x y /\ leR y x ==> x = y)``);

val q4950096_nonempty_chain_def = new_definition (
  "q4950096_nonempty_chain_def",
  ``q4950096_nonempty_chain
      (leR : 'a -> 'a -> bool) (c : 'a -> bool) <=>
      (?x. c x) /\
      (!x y.
        c x /\ c y /\ x <> y
        ==>
        leR x y \/ leR y x)``);

val q4950096_chain_complete_partial_order_def = new_definition (
  "q4950096_chain_complete_partial_order_def",
  ``q4950096_chain_complete_partial_order
      (leR : 'a -> 'a -> bool)
      (cSup : ('a -> bool) -> 'a) <=>
      q4950096_partial_order leR /\
      !c.
        q4950096_nonempty_chain leR c
        ==>
        (!x. c x ==> leR x (cSup c)) /\
        (!upper.
          (!x. c x ==> leR x upper)
          ==>
          leR (cSup c) upper)``);

val nonempty_fixedPoints_of_inflationary =
  ``!(leR : 'a -> 'a -> bool)
      (cSup : ('a -> bool) -> 'a)
      (f : 'a -> 'a).
      q4950096_chain_complete_partial_order leR cSup /\
      (!x. leR x (f x))
      ==>
      ?y. f y = y``;
