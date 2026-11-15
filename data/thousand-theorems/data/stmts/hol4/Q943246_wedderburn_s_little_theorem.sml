(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q943246, "Wedderburn's little theorem": every finite division ring has
  commutative multiplication, and hence is a field. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q943246_division_ring_def = new_definition (
  "q943246_division_ring_def",
  ``q943246_division_ring
      (zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (negR : 'a -> 'a)
      (mulR : 'a -> 'a -> 'a) (invR : 'a -> 'a) <=>
      zeroR <> oneR /\
      (!x y. addR x y = addR y x) /\
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x. addR zeroR x = x) /\
      (!x. addR (negR x) x = zeroR) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x. mulR oneR x = x /\ mulR x oneR = x) /\
      (!x. mulR zeroR x = zeroR /\ mulR x zeroR = zeroR) /\
      (!x y z. mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
      (!x y z. mulR (addR x y) z = addR (mulR x z) (mulR y z)) /\
      invR zeroR = zeroR /\
      (!x.
        x <> zeroR ==>
        mulR (invR x) x = oneR /\ mulR x (invR x) = oneR)``);

val q943246_field_def = new_definition (
  "q943246_field_def",
  ``q943246_field
      (zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (negR : 'a -> 'a)
      (mulR : 'a -> 'a -> 'a) (invR : 'a -> 'a) <=>
      q943246_division_ring zeroR oneR addR negR mulR invR /\
      (!x y. mulR x y = mulR y x)``);

val littleWedderburn =
  ``!(zeroR : 'a) (oneR : 'a)
      (addR : 'a -> 'a -> 'a) (negR : 'a -> 'a)
      (mulR : 'a -> 'a -> 'a) (invR : 'a -> 'a).
      q943246_division_ring zeroR oneR addR negR mulR invR /\
      FINITE (UNIV : 'a set)
      ==>
      q943246_field zeroR oneR addR negR mulR invR``;
