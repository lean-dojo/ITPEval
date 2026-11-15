(*
  Statement-only formalization of VERINA artifact verina_advanced_59,
  cataloged as "palindromeIgnoreNonAlnum": the executable Boolean program
  tests whether a Unicode-scalar string is a palindrome after removing
  non-ASCII-alphanumeric characters and lowercasing ASCII letters.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory;

val palindromeIgnoreNonAlnum_isUnicodeScalar_def = new_definition (
  "palindromeIgnoreNonAlnum_isUnicodeScalar_def",
  ``palindromeIgnoreNonAlnum_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val palindromeIgnoreNonAlnum_isUnicodeString_def = new_definition (
  "palindromeIgnoreNonAlnum_isUnicodeString_def",
  ``palindromeIgnoreNonAlnum_isUnicodeString (s : num list) <=>
      EVERY palindromeIgnoreNonAlnum_isUnicodeScalar s``
);

val palindromeIgnoreNonAlnum_isUpperAlpha_def = new_definition (
  "palindromeIgnoreNonAlnum_isUpperAlpha_def",
  ``palindromeIgnoreNonAlnum_isUpperAlpha (c : num) <=>
      65 <= c /\ c <= 90``
);

val palindromeIgnoreNonAlnum_isLowerAlpha_def = new_definition (
  "palindromeIgnoreNonAlnum_isLowerAlpha_def",
  ``palindromeIgnoreNonAlnum_isLowerAlpha (c : num) <=>
      97 <= c /\ c <= 122``
);

val palindromeIgnoreNonAlnum_isAlpha_def = new_definition (
  "palindromeIgnoreNonAlnum_isAlpha_def",
  ``palindromeIgnoreNonAlnum_isAlpha (c : num) <=>
      palindromeIgnoreNonAlnum_isUpperAlpha c \/
      palindromeIgnoreNonAlnum_isLowerAlpha c``
);

val palindromeIgnoreNonAlnum_isDigit_def = new_definition (
  "palindromeIgnoreNonAlnum_isDigit_def",
  ``palindromeIgnoreNonAlnum_isDigit (c : num) <=>
      48 <= c /\ c <= 57``
);

val palindromeIgnoreNonAlnum_toLower_def = new_definition (
  "palindromeIgnoreNonAlnum_toLower_def",
  ``palindromeIgnoreNonAlnum_toLower (c : num) =
      if palindromeIgnoreNonAlnum_isUpperAlpha c then c + 32 else c``
);

val palindromeIgnoreNonAlnum_clean_def = Define `
  (palindromeIgnoreNonAlnum_clean ([] : num list) = ([] : num list)) /\
  (palindromeIgnoreNonAlnum_clean (c::cs) =
     if palindromeIgnoreNonAlnum_isAlpha c \/
        palindromeIgnoreNonAlnum_isDigit c
     then
       palindromeIgnoreNonAlnum_toLower c::
         palindromeIgnoreNonAlnum_clean cs
     else
       palindromeIgnoreNonAlnum_clean cs)
`;

val palindromeIgnoreNonAlnum_precond_def = new_definition (
  "palindromeIgnoreNonAlnum_precond_def",
  ``palindromeIgnoreNonAlnum_precond (s : num list) <=> T``
);

val palindromeIgnoreNonAlnum_checkFuel_def = Define `
  (palindromeIgnoreNonAlnum_checkFuel
      0
      (left : num)
      (right : num)
      (cleaned : num list) =
     F) /\
  (palindromeIgnoreNonAlnum_checkFuel
      (SUC fuel)
      left
      right
      cleaned =
     if left >= right then
       T
     else if LLOOKUP cleaned left = LLOOKUP cleaned right then
       palindromeIgnoreNonAlnum_checkFuel
         fuel (left + 1) (right - 1) cleaned
     else
       F)
`;

val palindromeIgnoreNonAlnum_def = new_definition (
  "palindromeIgnoreNonAlnum_def",
  ``palindromeIgnoreNonAlnum (s : num list) =
      let cleaned = palindromeIgnoreNonAlnum_clean s in
      let n = LENGTH cleaned in
      let startIndex = 0 in
      let endIndex = if n = 0 then 0 else n - 1
      in
        palindromeIgnoreNonAlnum_checkFuel
          (SUC endIndex) startIndex endIndex cleaned``
);

val palindromeIgnoreNonAlnum_postcond_def = new_definition (
  "palindromeIgnoreNonAlnum_postcond_def",
  ``palindromeIgnoreNonAlnum_postcond
      (s : num list) (result : bool) <=>
      let cleaned = palindromeIgnoreNonAlnum_clean s in
      let forward = cleaned in
      let backward = REVERSE cleaned
      in
        if result then forward = backward else forward <> backward``
);

val palindromeIgnoreNonAlnum_spec_satisfied =
  ``!s : num list.
      palindromeIgnoreNonAlnum_isUnicodeString s ==>
      palindromeIgnoreNonAlnum_precond s ==>
      palindromeIgnoreNonAlnum_postcond
        s (palindromeIgnoreNonAlnum s)``;
