(*
  Statement-only formalization of VERINA corpus artifact verina_basic_67,
  catalog title "IsPalindrome": the executable Boolean program checks an
  arbitrary Unicode-character list with a recursive mirrored-index scan,
  under an always-true precondition and its pointwise palindrome correctness
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val IsPalindrome_isUnicodeScalar_def = new_definition (
  "IsPalindrome_isUnicodeScalar_def",
  ``IsPalindrome_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val IsPalindrome_isUnicodeString_def = new_definition (
  "IsPalindrome_isUnicodeString_def",
  ``IsPalindrome_isUnicodeString (x : num list) <=>
      EVERY IsPalindrome_isUnicodeScalar x``
);

val IsPalindrome_precond_def = new_definition (
  "IsPalindrome_precond_def",
  ``IsPalindrome_precond (x : num list) <=> T``
);

val isPalindromeHelperFuel_def = Define `
  (isPalindromeHelperFuel
      0
      (x : num list)
      (i : num)
      (j : num) =
     F) /\
  (isPalindromeHelperFuel
      (SUC fuel)
      x
      i
      j =
     if i < j then
       if i < LENGTH x /\ j < LENGTH x then
         if EL i x <> EL j x then
           F
         else
           isPalindromeHelperFuel
             fuel x (i + 1) (j - 1)
       else
         F
     else
       T)
`;

val isPalindromeHelper_def = new_definition (
  "isPalindromeHelper_def",
  ``isPalindromeHelper
      (x : num list) (i : num) (j : num) =
      isPalindromeHelperFuel (SUC j) x i j``
);

val IsPalindrome_def = new_definition (
  "IsPalindrome_def",
  ``IsPalindrome (x : num list) =
      if LENGTH x = 0 then
        T
      else
        isPalindromeHelper x 0 (LENGTH x - 1)``
);

val IsPalindrome_nthD_def = new_definition (
  "IsPalindrome_nthD_def",
  ``IsPalindrome_nthD (x : num list) (i : num) =
      if i < LENGTH x then EL i x else 0``
);

val IsPalindrome_postcond_def = new_definition (
  "IsPalindrome_postcond_def",
  ``IsPalindrome_postcond
      (x : num list) (result : bool) <=>
      (result = T <=>
       !i : num.
         i < LENGTH x ==>
         IsPalindrome_nthD x i =
         IsPalindrome_nthD x (LENGTH x - i - 1))``
);

val IsPalindrome_spec_satisfied =
  ``!x : num list.
      IsPalindrome_isUnicodeString x ==>
      IsPalindrome_precond x ==>
      IsPalindrome_postcond x (IsPalindrome x)``;
