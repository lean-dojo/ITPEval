(*
  Statement-only formalization of the Babel-formal topic comp_commute. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val cc_comp_def = new_definition (
  "cc_comp_def",
  ``cc_comp (g : 'b -> 'c) (f : 'a -> 'b) =
      \x. g (f x)``);

val cc_id_def = new_definition (
  "cc_id_def",
  ``cc_id (x : 'a) = x``);

val comp_assoc =
  ``!(h : 'c -> 'd) (g : 'b -> 'c) (f : 'a -> 'b).
      cc_comp h (cc_comp g f) = cc_comp (cc_comp h g) f``;

val comp_id_l =
  ``!(f : 'a -> 'b).
      cc_comp (cc_id : 'b -> 'b) f = f``;

val comp_id_r =
  ``!(f : 'a -> 'b).
      cc_comp f (cc_id : 'a -> 'a) = f``;

val cc_commute_def = new_definition (
  "cc_commute_def",
  ``cc_commute (f : 'a -> 'a) (g : 'a -> 'a) <=>
      cc_comp f g = cc_comp g f``);

val commute_symm =
  ``!(f : 'a -> 'a) g.
      cc_commute f g ==> cc_commute g f``;

val commute_with_id_l =
  ``!(f : 'a -> 'a).
      cc_commute f (cc_id : 'a -> 'a)``;

val commute_with_id_r =
  ``!(f : 'a -> 'a).
      cc_commute (cc_id : 'a -> 'a) f``;

val commute_refl =
  ``!(f : 'a -> 'a).
      cc_commute f f``;

val commute_congr =
  ``!(f1 : 'a -> 'a) f2 g1 g2.
      f1 = f2 ==>
      g1 = g2 ==>
      cc_commute f1 g1 ==>
      cc_commute f2 g2``;

val commute_transport_left_id =
  ``!(f : 'a -> 'a) g.
      cc_commute f g ==>
      cc_commute (cc_comp (cc_id : 'a -> 'a) f) g``;

val commute_transport_right_id =
  ``!(f : 'a -> 'a) g.
      cc_commute f g ==>
      cc_commute f (cc_comp (cc_id : 'a -> 'a) g)``;
