(*
  Statement-only formalization of VERINA artifact verina_advanced_61,
  cataloged as "productExceptSelf": the executable prefix-and-suffix product
  program returns, at each integer-list index, the product of every other
  entry and satisfies its stated length and indexing contract. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val productExceptSelf_precond_def = new_definition (
  "productExceptSelf_precond_def",
  ``productExceptSelf_precond (nums : int list) <=> T``
);

val productExceptSelf_lastDefault_def = Define `
  (productExceptSelf_lastDefault ([] : int list) = (0 : int)) /\
  (productExceptSelf_lastDefault (x::xs) =
     if xs = [] then x
     else productExceptSelf_lastDefault xs)
`;

val productExceptSelf_prefixFold_def = Define `
  (productExceptSelf_prefixFold
      ([] : int list)
      (acc : int list) =
     acc) /\
  (productExceptSelf_prefixFold
      (x::xs)
      acc =
     productExceptSelf_prefixFold
       xs
       (acc ++ [productExceptSelf_lastDefault acc * x]))
`;

val computepref_def = new_definition (
  "computepref_def",
  ``computepref (nums : int list) =
      productExceptSelf_prefixFold nums [1]``
);

val computeSuffix_def = new_definition (
  "computeSuffix_def",
  ``computeSuffix (nums : int list) =
      REVERSE (computepref (REVERSE nums))``
);

val productExceptSelf_getDefault_def = new_definition (
  "productExceptSelf_getDefault_def",
  ``productExceptSelf_getDefault
      (xs : int list) (index : num) =
      if index < LENGTH xs then EL index xs else (0 : int)``
);

val productExceptSelf_def = new_definition (
  "productExceptSelf_def",
  ``productExceptSelf (nums : int list) =
      let n = LENGTH nums in
      if n = 0 then
        []
      else
        let pref = computepref nums in
        let suffix = computeSuffix nums in
          MAP
            (\i : num.
               productExceptSelf_getDefault pref i *
               productExceptSelf_getDefault suffix (i + 1))
            (COUNT_LIST n)``
);

val productExceptSelf_myprod_def = Define `
  (productExceptSelf_myprod ([] : int list) = (1 : int)) /\
  (productExceptSelf_myprod (x::xs) =
     x * productExceptSelf_myprod xs)
`;

val productExceptSelf_getOpt_def = new_definition (
  "productExceptSelf_getOpt_def",
  ``productExceptSelf_getOpt
      (xs : int list) (index : num) =
      if index < LENGTH xs then
        SOME (EL index xs)
      else
        (NONE : int option)``
);

val productExceptSelf_postcond_def = new_definition (
  "productExceptSelf_postcond_def",
  ``productExceptSelf_postcond
      (nums : int list) (result : int list) <=>
      LENGTH nums = LENGTH result /\
      EVERY
        (\i : num.
           productExceptSelf_getOpt result i =
           SOME
             (productExceptSelf_myprod (TAKE i nums) *
              productExceptSelf_myprod (DROP (i + 1) nums)))
        (COUNT_LIST (LENGTH nums))``
);

val productExceptSelf_spec_satisfied =
  ``!nums : int list.
      productExceptSelf_precond nums ==>
      productExceptSelf_postcond
        nums (productExceptSelf nums)``;
