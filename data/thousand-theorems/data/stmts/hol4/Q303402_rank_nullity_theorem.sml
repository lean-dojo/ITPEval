(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q303402, "Rank–nullity theorem": for a linear map between modules over an
  arbitrary ring satisfying the rank-nullity condition, the cardinal rank of
  its range plus the cardinal rank of its kernel equals the cardinal rank of
  its domain. This file contains no proof.
*)

open HolKernel Parse boolLib;
open cardinalTheory pred_setTheory;

val q303402_ring_def = new_definition (
  "q303402_ring_def",
  ``q303402_ring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r) <=>
      (!a b. addR a b = addR b a) /\
      (!a b c. addR (addR a b) c = addR a (addR b c)) /\
      (!a. addR zeroR a = a) /\
      (!a. addR (negR a) a = zeroR) /\
      (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\
      (!a. mulR oneR a = a) /\
      (!a. mulR a oneR = a) /\
      (!a b c. mulR a (addR b c) =
                 addR (mulR a b) (mulR a c)) /\
      (!a b c. mulR (addR a b) c =
                 addR (mulR a c) (mulR b c))``);

val q303402_module_def = new_definition (
  "q303402_module_def",
  ``q303402_module
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (smul : 'r -> 'm -> 'm) <=>
      (!x y. addM x y = addM y x) /\
      (!x y z. addM (addM x y) z = addM x (addM y z)) /\
      (!x. addM zeroM x = x) /\
      (!x. addM (negM x) x = zeroM) /\
      (!a x y. smul a (addM x y) =
                 addM (smul a x) (smul a y)) /\
      (!a b x. smul (addR a b) x =
                 addM (smul a x) (smul b x)) /\
      (!a b x. smul (mulR a b) x = smul a (smul b x)) /\
      (!x. smul oneR x = x) /\
      (!x. smul zeroR x = zeroM) /\
      (!a. smul a zeroM = zeroM)``);

val q303402_linear_map_def = new_definition (
  "q303402_linear_map_def",
  ``q303402_linear_map
      (addM : 'm -> 'm -> 'm) (smulM : 'r -> 'm -> 'm)
      (addN : 'n -> 'n -> 'n) (smulN : 'r -> 'n -> 'n)
      (f : 'm -> 'n) <=>
      (!x y. f (addM x y) = addN (f x) (f y)) /\
      (!a x. f (smulM a x) = smulN a (f x))``);

val q303402_submodule_def = new_definition (
  "q303402_submodule_def",
  ``q303402_submodule
      (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (s : 'm set) <=>
      zeroM IN s /\
      (!x y. x IN s /\ y IN s ==> addM x y IN s) /\
      (!x. x IN s ==> negM x IN s) /\
      (!a x. x IN s ==> smul a x IN s)``);

val q303402_lincomb_def = new_definition (
  "q303402_lincomb_def",
  ``q303402_lincomb
      (zeroR : 'r) (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (s : 'm set) (coeff : 'm -> 'r) =
      ITSET
        (\x acc. addM (smul (coeff x) x) acc)
        {x | x IN s /\ coeff x <> zeroR}
        zeroM``);

val q303402_linear_independent_def = new_definition (
  "q303402_linear_independent_def",
  ``q303402_linear_independent
      (zeroR : 'r) (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (s : 'm set) <=>
      !coeff : 'm -> 'r.
        FINITE {x | x IN s /\ coeff x <> zeroR} /\
        q303402_lincomb zeroR zeroM addM smul s coeff = zeroM
        ==>
        !x. x IN s ==> coeff x = zeroR``);

val q303402_rank_witness_def = new_definition (
  "q303402_rank_witness_def",
  ``q303402_rank_witness
      (zeroR : 'r) (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (carrier : 'm set) (b : 'm set) <=>
      b SUBSET carrier /\
      q303402_linear_independent zeroR zeroM addM smul b /\
      (!s : 'm set.
        s SUBSET carrier /\
        q303402_linear_independent zeroR zeroM addM smul s
        ==>
        s <<= b)``);

val q303402_coset_def = new_definition (
  "q303402_coset_def",
  ``q303402_coset
      (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (s : 'm set) (x : 'm) =
      {y | addM y (negM x) IN s}``);

val q303402_quotient_carrier_def = new_definition (
  "q303402_quotient_carrier_def",
  ``q303402_quotient_carrier
      (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm) (s : 'm set) =
      {c : 'm set | ?x. c = q303402_coset addM negM s x}``);

val q303402_representative_def = new_definition (
  "q303402_representative_def",
  ``q303402_representative
      (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (s : 'm set) (c : 'm set) =
      @x. c = q303402_coset addM negM s x``);

val q303402_quotient_add_def = new_definition (
  "q303402_quotient_add_def",
  ``q303402_quotient_add
      (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (s : 'm set) (c : 'm set) (d : 'm set) =
      q303402_coset addM negM s
        (addM
          (q303402_representative addM negM s c)
          (q303402_representative addM negM s d))``);

val q303402_quotient_smul_def = new_definition (
  "q303402_quotient_smul_def",
  ``q303402_quotient_smul
      (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (smul : 'r -> 'm -> 'm) (s : 'm set)
      (a : 'r) (c : 'm set) =
      q303402_coset addM negM s
        (smul a (q303402_representative addM negM s c))``);

val q303402_has_rank_nullity_def = new_definition (
  "q303402_has_rank_nullity_def",
  ``q303402_has_rank_nullity
      (zeroR : 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (smul : 'r -> 'm -> 'm) <=>
      !s : 'm set.
        q303402_submodule zeroM addM negM smul s
        ==>
        ?bq : ('m set) set.
        ?bs bm : 'm set.
          q303402_rank_witness
            zeroR
            (q303402_coset addM negM s zeroM)
            (q303402_quotient_add addM negM s)
            (q303402_quotient_smul addM negM smul s)
            (q303402_quotient_carrier addM negM s) bq /\
          q303402_rank_witness zeroR zeroM addM smul s bs /\
          q303402_rank_witness zeroR zeroM addM smul UNIV bm /\
          (IMAGE INL bq UNION IMAGE INR bs) =~ bm``);

val LinearMap_rank_range_add_rank_ker =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (negR : 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm) (negM : 'm -> 'm)
      (smulM : 'r -> 'm -> 'm)
      (zeroN : 'n) (addN : 'n -> 'n -> 'n) (negN : 'n -> 'n)
      (smulN : 'r -> 'n -> 'n)
      (f : 'm -> 'n).
      q303402_ring zeroR oneR addR mulR negR /\
      q303402_module zeroR oneR addR mulR
        zeroM addM negM smulM /\
      q303402_module zeroR oneR addR mulR
        zeroN addN negN smulN /\
      q303402_linear_map addM smulM addN smulN f /\
      q303402_has_rank_nullity zeroR zeroM addM negM smulM /\
      q303402_has_rank_nullity zeroR zeroN addN negN smulN
      ==>
      ?br : 'n set.
      ?bk bm : 'm set.
        q303402_rank_witness zeroR zeroN addN smulN
          {y | ?x. f x = y} br /\
        q303402_rank_witness zeroR zeroM addM smulM
          {x | f x = zeroN} bk /\
        q303402_rank_witness zeroR zeroM addM smulM UNIV bm /\
        (IMAGE INL br UNION IMAGE INR bk) =~ bm``;
