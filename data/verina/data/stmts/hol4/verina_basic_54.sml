(*
  Statement-only formalization of VERINA corpus artifact verina_basic_54,
  catalog title "CanyonSearch": the executable two-pointer search scans two
  nonempty pairwise nondecreasing integer arrays, maintaining and returning
  an attained minimum absolute difference. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val CanyonSearch_pairwiseLe_def = Define `
  (CanyonSearch_pairwiseLe ([] : int list) = T) /\
  (CanyonSearch_pairwiseLe (x::xs) =
     (EVERY (\y : int. x <= y) xs /\
      CanyonSearch_pairwiseLe xs))
`;

val CanyonSearch_precond_def = new_definition (
  "CanyonSearch_precond_def",
  ``CanyonSearch_precond
      (a : int list) (b : int list) <=>
      0 < LENGTH a /\
      0 < LENGTH b /\
      CanyonSearch_pairwiseLe a /\
      CanyonSearch_pairwiseLe b``
);

val CanyonSearch_nthD_def = Define `
  (CanyonSearch_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (CanyonSearch_nthD
      0 (x::xs) = x) /\
  (CanyonSearch_nthD
      (SUC index) (x::xs) =
     CanyonSearch_nthD index xs)
`;

val CanyonSearch_natAbsDiff_def = new_definition (
  "CanyonSearch_natAbsDiff_def",
  ``CanyonSearch_natAbsDiff (x : int) (y : int) =
      Num (ABS (x - y))``
);

val canyonSearchAuxFuel_def = Define `
  (canyonSearchAuxFuel
      0
      (a : int list) (b : int list)
      (m : num) (n : num) (d : num) =
     d) /\
  (canyonSearchAuxFuel
      (SUC fuel) a b m n d =
     if m < LENGTH a /\ n < LENGTH b then
       let am = CanyonSearch_nthD m a in
       let bn = CanyonSearch_nthD n b in
       let diff = CanyonSearch_natAbsDiff am bn in
       let new_d = if diff < d then diff else d in
         if am <= bn then
           canyonSearchAuxFuel fuel a b (m + 1) n new_d
         else
           canyonSearchAuxFuel fuel a b m (n + 1) new_d
     else
       d)
`;

val canyonSearchAux_def = new_definition (
  "canyonSearchAux_def",
  ``canyonSearchAux
      (a : int list) (b : int list)
      (m : num) (n : num) (d : num) =
      canyonSearchAuxFuel
        ((LENGTH a - m) + (LENGTH b - n))
        a b m n d``
);

val CanyonSearch_def = new_definition (
  "CanyonSearch_def",
  ``CanyonSearch (a : int list) (b : int list) =
      let a0 = CanyonSearch_nthD 0 a in
      let b0 = CanyonSearch_nthD 0 b in
      let init =
        if a0 < b0 then
          CanyonSearch_natAbsDiff b0 a0
        else
          CanyonSearch_natAbsDiff a0 b0
      in
        canyonSearchAux a b 0 0 init``
);

val CanyonSearch_postcond_def = new_definition (
  "CanyonSearch_postcond_def",
  ``CanyonSearch_postcond
      (a : int list) (b : int list) (result : num) <=>
      EXISTS
        (\ai : int.
           EXISTS
             (\bi : int.
                result = CanyonSearch_natAbsDiff ai bi)
             b)
        a /\
      EVERY
        (\ai : int.
           EVERY
             (\bi : int.
                result <= CanyonSearch_natAbsDiff ai bi)
             b)
        a``
);

val CanyonSearch_spec_satisfied =
  ``!(a : int list) (b : int list).
      CanyonSearch_precond a b ==>
      CanyonSearch_postcond
        a b (CanyonSearch a b)``;
