(*
  Statement-only formalization of the Babel-formal artifact limits_uniqueness:
  uniqueness of a sequence limit in an abstract absolute-value setting. This
  file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_theory "hello";

val limits_abs_field_def = new_definition (
  "limits_abs_field_def",
  ``limits_abs_field
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (absV : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (natLe : 'n -> 'n -> bool) (natMax : 'n -> 'n -> 'n) <=>
      (!x y. natLe x (natMax x y)) /\
      (!x y. natLe y (natMax x y)) /\
      (!x y. addR x y = addR y x) /\
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x. addR x zeroR = x) /\
      (!x. addR x (oppR x) = zeroR) /\
      (!x y. oppR (addR x y) = addR (oppR x) (oppR y)) /\
      (!x y. mulR x y = mulR y x) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x. mulR x oneR = x) /\
      (!x. leR x x) /\
      (!x y z. leR x y ==> leR y z ==> leR x z) /\
      (!a b c d.
         leR a b ==> leR c d ==> leR (addR a c) (addR b d)) /\
      (!x. leR zeroR (absV x)) /\
      (!x y.
         leR (absV (addR x y)) (addR (absV x) (absV y))) /\
      (!x. absV (oppR x) = absV x) /\
      (!x y.
         absV (addR x (oppR y)) = absV (addR y (oppR x))) /\
      (!x y z.
         addR x (oppR z) =
           addR (addR x (oppR y)) (addR y (oppR z))) /\
      (!x y. addR x (oppR y) = zeroR ==> x = y) /\
      (!x.
         (!eps.
            ltR zeroR eps ==>
            leR (absV x) (addR eps eps)) ==>
         x = zeroR)``);

val limits_sub_def = new_definition (
  "limits_sub_def",
  ``limits_sub (addR : 'r -> 'r -> 'r) (oppR : 'r -> 'r) x y =
      addR x (oppR y)``);

val limits_limit_def = new_definition (
  "limits_limit_def",
  ``limits_limit
      (zeroR : 'r) (addR : 'r -> 'r -> 'r) (oppR : 'r -> 'r)
      (absV : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (natLe : 'n -> 'n -> bool) (u : 'n -> 'r) (l : 'r) <=>
      !eps.
        ltR zeroR eps ==>
        ?N. !n.
          natLe N n ==>
          leR (absV (limits_sub addR oppR (u n) l)) eps``);

val sub_self_zero =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (absV : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (natLe : 'n -> 'n -> bool) (natMax : 'n -> 'n -> 'n).
      limits_abs_field zeroR oneR addR mulR oppR absV
        leR ltR natLe natMax ==>
      !x. limits_sub addR oppR x x = zeroR``;

val sub_decomp =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (absV : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (natLe : 'n -> 'n -> bool) (natMax : 'n -> 'n -> 'n).
      limits_abs_field zeroR oneR addR mulR oppR absV
        leR ltR natLe natMax ==>
      !x y z.
        limits_sub addR oppR x z =
          addR (limits_sub addR oppR x y)
               (limits_sub addR oppR y z)``;

val abs_sub_triangle =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (absV : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (natLe : 'n -> 'n -> bool) (natMax : 'n -> 'n -> 'n).
      limits_abs_field zeroR oneR addR mulR oppR absV
        leR ltR natLe natMax ==>
      !x y z.
        leR (absV (limits_sub addR oppR x z))
          (addR (absV (limits_sub addR oppR x y))
                (absV (limits_sub addR oppR y z)))``;

val abs_sub_nonneg =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (absV : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (natLe : 'n -> 'n -> bool) (natMax : 'n -> 'n -> 'n).
      limits_abs_field zeroR oneR addR mulR oppR absV
        leR ltR natLe natMax ==>
      !x y. leR zeroR (absV (limits_sub addR oppR x y))``;

val limit_unique =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (absV : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (natLe : 'n -> 'n -> bool) (natMax : 'n -> 'n -> 'n)
      (u : 'n -> 'r) (l : 'r) (m : 'r).
      limits_abs_field zeroR oneR addR mulR oppR absV
        leR ltR natLe natMax ==>
      limits_limit zeroR addR oppR absV leR ltR natLe u l ==>
      limits_limit zeroR addR oppR absV leR ltR natLe u m ==>
      l = m``;

val _ = export_theory();
