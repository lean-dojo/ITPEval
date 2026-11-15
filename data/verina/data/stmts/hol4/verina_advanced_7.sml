(*
  Statement-only formalization of VERINA artifact verina_advanced_7,
  cataloged as "binaryToDecimal": the executable recursive program converts
  a big-endian list of binary natural-number digits to its decimal value and
  satisfies the stated fold-based contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val binaryToDecimal_precond_def = new_definition (
  "binaryToDecimal_precond_def",
  ``binaryToDecimal_precond (digits : num list) <=>
      EVERY (\d : num. d = 0 \/ d = 1) digits``
);

val binaryToDecimal_helper_def = Define `
  (binaryToDecimal_helper ([] : num list) = 0) /\
  (binaryToDecimal_helper (first::rest) =
     first * 2 EXP LENGTH rest + binaryToDecimal_helper rest)
`;

val binaryToDecimal_def = new_definition (
  "binaryToDecimal_def",
  ``binaryToDecimal (digits : num list) =
      binaryToDecimal_helper digits``
);

val binaryToDecimal_postcond_def = new_definition (
  "binaryToDecimal_postcond_def",
  ``binaryToDecimal_postcond
      (digits : num list) (result : num) <=>
      result - FOLDL (\acc bit. acc * 2 + bit) 0 digits = 0 /\
      FOLDL (\acc bit. acc * 2 + bit) 0 digits - result = 0``
);

val binaryToDecimal_spec_satisfied =
  ``!digits : num list.
      binaryToDecimal_precond digits ==>
      binaryToDecimal_postcond digits (binaryToDecimal digits)``;
