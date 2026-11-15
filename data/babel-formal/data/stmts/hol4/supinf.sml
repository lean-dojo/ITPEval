(*
  Statement-only formalization of the Babel-formal artifact supinf: bounds,
  infima, sequence limits, and reciprocal-successor estimates in an abstract
  complete ordered field. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_theory "hello";

val supinf_context_def = new_definition (
  "supinf_context_def",
  ``supinf_context
      (zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r) <=>
      (!n. natLe n n) /\
      (!n m. natLe n m ==> natLe n (succN m)) /\
      (!n. natLe n (succN n)) /\
      (!x y. addR x y = addR y x) /\
      (!x y z. addR (addR x y) z = addR x (addR y z)) /\
      (!x. addR x zeroR = x) /\
      (!x. addR (oppR x) x = zeroR) /\
      (!x y. mulR x y = mulR y x) /\
      (!x y z. mulR (mulR x y) z = mulR x (mulR y z)) /\
      (!x. mulR x oneR = x) /\
      (!x y z. mulR x (addR y z) = addR (mulR x y) (mulR x z)) /\
      (!x. addR x (oppR zeroR) = x) /\
      (!x. leR x x) /\
      (!x y z. leR x y ==> leR y z ==> leR x z) /\
      (!x y. leR x y ==> leR y x ==> x = y) /\
      (!x y. ltR x y <=> leR x y /\ ~(x = y)) /\
      (!x. leR (addR x (oppR zeroR)) (absR x)) /\
      (!x. ltR zeroR x ==> ltR zeroR (invR x)) /\
      (!x y z. leR y z ==> leR (addR x y) (addR x z)) /\
      (!x. ltR zeroR x ==> invR (invR x) = x) /\
      (!n. ltR zeroR (ofNat (succN n))) /\
      (!m n. natLe m n ==> leR (ofNat m) (ofNat n)) /\
      ofNat zeroNat = zeroR /\
      (!n. ofNat (succN n) = addR (ofNat n) oneR) /\
      (!x y. ltR x y \/ x = y \/ ltR y x) /\
      (!a b.
         ltR zeroR a ==>
         ltR zeroR b ==>
         leR a b ==>
         leR (invR b) (invR a)) /\
      (!x y.
         ltR x y ==>
         ?eps. ltR zeroR eps /\ ltR (addR x eps) y) /\
      (!x. ?n. leR x (ofNat n)) /\
      (!A.
         (?ub. !a. A a ==> leR ub a) ==>
         ?sup.
           (!a. A a ==> leR a sup) /\
           (!y. (!a. A a ==> leR a y) ==> leR sup y))``);

val supinf_sub_def = new_definition (
  "supinf_sub_def",
  ``supinf_sub (addR : 'r -> 'r -> 'r) (oppR : 'r -> 'r) x y =
      addR x (oppR y)``);

val supinf_up_bounds_def = new_definition (
  "supinf_up_bounds_def",
  ``supinf_up_bounds (leR : 'r -> 'r -> bool)
                     (A : 'r -> bool) x <=>
      !a. A a ==> leR a x``);

val supinf_is_maximum_def = new_definition (
  "supinf_is_maximum_def",
  ``supinf_is_maximum (leR : 'r -> 'r -> bool)
                      (A : 'r -> bool) x <=>
      A x /\ supinf_up_bounds leR A x``);

val supinf_low_bounds_def = new_definition (
  "supinf_low_bounds_def",
  ``supinf_low_bounds (leR : 'r -> 'r -> bool)
                      (A : 'r -> bool) x <=>
      !a. A a ==> leR x a``);

val supinf_is_inf_def = new_definition (
  "supinf_is_inf_def",
  ``supinf_is_inf (leR : 'r -> 'r -> bool)
                  (A : 'r -> bool) x <=>
      supinf_is_maximum leR (supinf_low_bounds leR A) x``);

val supinf_limit_def = new_definition (
  "supinf_limit_def",
  ``supinf_limit
      (zeroR : 'r) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (leR : 'r -> 'r -> bool)
      (addR : 'r -> 'r -> 'r) (oppR : 'r -> 'r)
      (natLe : 'n -> 'n -> bool) (u : 'n -> 'r) (l : 'r) <=>
      !eps.
        ltR zeroR eps ==>
        ?N. !n.
          natLe N n ==>
          leR (absR (supinf_sub addR oppR (u n) l)) eps``);

val add_sub_cancel_r =
  ``!(zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r) a b.
      supinf_context zeroNat succN natLe zeroR oneR addR mulR
        oppR invR leR ltR absR ofNat ==>
      addR a (supinf_sub addR oppR b a) = b``;

val rabs_pos =
  ``!(zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r) t.
      supinf_context zeroNat succN natLe zeroR oneR addR mulR
        oppR invR leR ltR absR ofNat ==>
      leR t (absR t)``;

val unique_max =
  ``!(zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r)
      (A : 'r -> bool) x y.
      supinf_context zeroNat succN natLe zeroR oneR addR mulR
        oppR invR leR ltR absR ofNat ==>
      supinf_is_maximum leR A x ==>
      supinf_is_maximum leR A y ==>
      x = y``;

val inf_lt =
  ``!(zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r)
      (A : 'r -> bool) x y.
      supinf_context zeroNat succN natLe zeroR oneR addR mulR
        oppR invR leR ltR absR ofNat ==>
      supinf_is_inf leR A x ==>
      ltR x y ==>
      ?a. A a /\ ltR a y``;

val le_of_le_add_eps =
  ``!(zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r) x y.
      supinf_context zeroNat succN natLe zeroR oneR addR mulR
        oppR invR leR ltR absR ofNat ==>
      (!eps. ltR zeroR eps ==> leR y (addR x eps)) ==>
      leR y x``;

val le_lim =
  ``!(zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r)
      (u : 'n -> 'r) x y.
      supinf_context zeroNat succN natLe zeroR oneR addR mulR
        oppR invR leR ltR absR ofNat ==>
      supinf_limit zeroR ltR absR leR addR oppR natLe u x ==>
      (!n. leR y (u n)) ==>
      leR y x``;

val inv_succ_pos =
  ``!(zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r) n.
      supinf_context zeroNat succN natLe zeroR oneR addR mulR
        oppR invR leR ltR absR ofNat ==>
      ltR zeroR (invR (ofNat (succN n)))``;

val limit_inv_succ =
  ``!(zeroNat : 'n) (succN : 'n -> 'n)
      (natLe : 'n -> 'n -> bool)
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (oppR : 'r -> 'r) (invR : 'r -> 'r)
      (leR : 'r -> 'r -> bool) (ltR : 'r -> 'r -> bool)
      (absR : 'r -> 'r) (ofNat : 'n -> 'r) eps.
      supinf_context zeroNat succN natLe zeroR oneR addR mulR
        oppR invR leR ltR absR ofNat ==>
      ltR zeroR eps ==>
      ?N. !n.
        natLe N n ==>
        leR (invR (ofNat (succN n))) eps``;

val _ = export_theory();
