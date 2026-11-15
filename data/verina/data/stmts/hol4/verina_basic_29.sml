(*
  Statement-only formalization of VERINA corpus artifact verina_basic_29,
  catalog title "removeElement": the executable index-erasure program removes
  the valid k-th integer from an array, preserves the preceding elements, and
  shifts the following elements one position left. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val removeElement_precond_def = new_definition (
  "removeElement_precond_def",
  ``removeElement_precond (s : int list) (k : num) <=>
      k < LENGTH s``
);

val removeElement_eraseIdx_def = Define `
  (removeElement_eraseIdx
      ([] : int list) (k : num) =
     ([] : int list)) /\
  (removeElement_eraseIdx (x::xs) 0 = xs) /\
  (removeElement_eraseIdx (x::xs) (SUC k) =
     x::removeElement_eraseIdx xs k)
`;

val removeElement_def = new_definition (
  "removeElement_def",
  ``removeElement (s : int list) (k : num) =
      removeElement_eraseIdx s k``
);

val removeElement_postcond_def = new_definition (
  "removeElement_postcond_def",
  ``removeElement_postcond
      (s : int list) (k : num) (result : int list) <=>
      LENGTH result = LENGTH s - 1 /\
      (!i : num.
         i < k ==>
         EL i result = EL i s) /\
      (!i : num.
         i < LENGTH result ==>
         i >= k ==>
         EL i result = EL (i + 1) s)``
);

val removeElement_spec_satisfied =
  ``!(s : int list) (k : num).
      removeElement_precond s k ==>
      removeElement_postcond s k (removeElement s k)``;
