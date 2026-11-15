(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527263, "Kleene fixed-point theorem": the least fixed point of an
  omega-Scott-continuous order endomorphism of a complete lattice is the
  supremum of its finite iterates from bottom. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val q3527263_complete_lattice_def = new_definition (
  "q3527263_complete_lattice_def",
  ``q3527263_complete_lattice
      (leR : 'a -> 'a -> bool)
      (supR : ('a -> bool) -> 'a)
      (infR : ('a -> bool) -> 'a) <=>
      (!x. leR x x) /\
      (!x y z. leR x y ==> leR y z ==> leR x z) /\
      (!x y. leR x y ==> leR y x ==> x = y) /\
      (!P x. P x ==> leR x (supR P)) /\
      (!P upper.
         (!x. P x ==> leR x upper) ==>
         leR (supR P) upper) /\
      (!P x. P x ==> leR (infR P) x) /\
      (!P lower.
         (!x. P x ==> leR lower x) ==>
         leR lower (infR P))``);

val q3527263_order_endomorphism_def = new_definition (
  "q3527263_order_endomorphism_def",
  ``q3527263_order_endomorphism
      (leR : 'a -> 'a -> bool) (f : 'a -> 'a) <=>
      !x y. leR x y ==> leR (f x) (f y)``);

val q3527263_chain_def = new_definition (
  "q3527263_chain_def",
  ``q3527263_chain
      (leR : 'a -> 'a -> bool) (c : num -> 'a) <=>
      !m n : num. m <= n ==> leR (c m) (c n)``);

val q3527263_omega_scott_continuous_def = new_definition (
  "q3527263_omega_scott_continuous_def",
  ``q3527263_omega_scott_continuous
      (leR : 'a -> 'a -> bool)
      (supR : ('a -> bool) -> 'a)
      (f : 'a -> 'a) <=>
      !c : num -> 'a.
        q3527263_chain leR c ==>
        f (supR (\x. ?n : num. x = c n)) =
        supR (\y. ?n : num. y = f (c n))``);

val q3527263_bottom_def = new_definition (
  "q3527263_bottom_def",
  ``q3527263_bottom (supR : ('a -> bool) -> 'a) =
      supR (\x : 'a. F)``);

val q3527263_lfp_def = new_definition (
  "q3527263_lfp_def",
  ``q3527263_lfp
      (leR : 'a -> 'a -> bool)
      (infR : ('a -> bool) -> 'a)
      (f : 'a -> 'a) =
      infR (\x. leR (f x) x)``);

val q3527263_iterates_supremum_def = new_definition (
  "q3527263_iterates_supremum_def",
  ``q3527263_iterates_supremum
      (supR : ('a -> bool) -> 'a) (f : 'a -> 'a) =
      supR
        (\x.
          ?n : num.
            x = FUNPOW f n (q3527263_bottom supR))``);

val lfp_eq_sSup_iterate =
  ``!(leR : 'a -> 'a -> bool)
      (supR : ('a -> bool) -> 'a)
      (infR : ('a -> bool) -> 'a)
      (f : 'a -> 'a).
      q3527263_complete_lattice leR supR infR /\
      q3527263_order_endomorphism leR f /\
      q3527263_omega_scott_continuous leR supR f
      ==>
      q3527263_lfp leR infR f =
      q3527263_iterates_supremum supR f``;
