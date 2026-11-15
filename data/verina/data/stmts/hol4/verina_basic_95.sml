(*
  Statement-only formalization of VERINA corpus artifact verina_basic_95,
  catalog title "swap": the executable integer-array program exchanges the
  elements at two valid integer indices, preserves the array length and all
  other elements, and satisfies its swap contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val swap_toNat_def = new_definition (
  "swap_toNat_def",
  ``swap_toNat (i : int) =
      if i < 0 then 0 else Num i``
);

val swap_getBang_def = new_definition (
  "swap_getBang_def",
  ``swap_getBang (arr : int list) (i : num) =
      if i < LENGTH arr then EL i arr else (0 : int)``
);

val swap_setBang_def = new_definition (
  "swap_setBang_def",
  ``swap_setBang
      (arr : int list) (i : num) (value : int) =
      if i < LENGTH arr then LUPDATE value i arr else arr``
);

val swap_precond_def = new_definition (
  "swap_precond_def",
  ``swap_precond (arr : int list) (i : int) (j : int) <=>
      0 <= i /\
      0 <= j /\
      swap_toNat i < LENGTH arr /\
      swap_toNat j < LENGTH arr``
);

val swap_def = new_definition (
  "swap_def",
  ``swap (arr : int list) (i : int) (j : int) =
      let i_nat = swap_toNat i in
      let j_nat = swap_toNat j in
      let arr1 =
        swap_setBang arr i_nat (swap_getBang arr j_nat)
      in
      let arr2 =
        swap_setBang arr1 j_nat (swap_getBang arr i_nat)
      in
        arr2``
);

val swap_postcond_def = new_definition (
  "swap_postcond_def",
  ``swap_postcond
      (arr : int list) (i : int) (j : int) (result : int list) <=>
      LENGTH result = LENGTH arr /\
      swap_getBang result (swap_toNat i) =
        swap_getBang arr (swap_toNat j) /\
      swap_getBang result (swap_toNat j) =
        swap_getBang arr (swap_toNat i) /\
      (!k : num.
         k < LENGTH arr ==>
         k <> swap_toNat i ==>
         k <> swap_toNat j ==>
         swap_getBang result k = swap_getBang arr k)``
);

val swap_spec_satisfied =
  ``!(arr : int list) (i : int) (j : int).
      swap_precond arr i j ==>
      swap_postcond arr i j (swap arr i j)``;
