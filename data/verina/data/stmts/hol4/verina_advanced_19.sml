(*
  Statement-only formalization of VERINA artifact verina_advanced_19,
  cataloged as "isCleanPalindrome": the executable Boolean program tests
  whether the Unicode-scalar string's ASCII letters form a
  case-insensitive palindrome after all other characters are removed.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory;

val isUnicodeScalar_def = new_definition (
  "isUnicodeScalar_def",
  ``isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val isUnicodeString_def = new_definition (
  "isUnicodeString_def",
  ``isUnicodeString (s : num list) <=> EVERY isUnicodeScalar s``
);

val isUpperAlpha_def = new_definition (
  "isUpperAlpha_def",
  ``isUpperAlpha (c : num) <=> 65 <= c /\ c <= 90``
);

val isLowerAlpha_def = new_definition (
  "isLowerAlpha_def",
  ``isLowerAlpha (c : num) <=> 97 <= c /\ c <= 122``
);

val isAlpha_def = new_definition (
  "isAlpha_def",
  ``isAlpha (c : num) <=> isUpperAlpha c \/ isLowerAlpha c``
);

val toLower_def = new_definition (
  "toLower_def",
  ``toLower (c : num) = if isUpperAlpha c then c + 32 else c``
);

val normalizeChar_def = new_definition (
  "normalizeChar_def",
  ``normalizeChar (c : num) =
      if isAlpha c then SOME (toLower c) else NONE``
);

val normalizeString_def = Define `
  (normalizeString ([] : num list) = ([] : num list)) /\
  (normalizeString (c::cs) =
     case normalizeChar c of
       NONE => normalizeString cs
     | SOME c' => c'::normalizeString cs)
`;

val isCleanPalindrome_precond_def = new_definition (
  "isCleanPalindrome_precond_def",
  ``isCleanPalindrome_precond (s : num list) <=> T``
);

val reverseList_def = new_definition (
  "reverseList_def",
  ``reverseList (xs : num list) = REVERSE xs``
);

val isCleanPalindrome_def = new_definition (
  "isCleanPalindrome_def",
  ``isCleanPalindrome (s : num list) =
      let norm = normalizeString s
      in
        (norm = reverseList norm)``
);

val isCleanPalindrome_postcond_def = new_definition (
  "isCleanPalindrome_postcond_def",
  ``isCleanPalindrome_postcond
      (s : num list) (result : bool) <=>
      let norm = normalizeString s
      in
        (result = T ==> norm = REVERSE norm) /\
        (result = F ==> norm <> REVERSE norm)``
);

val isCleanPalindrome_spec_satisfied =
  ``!s : num list.
      isUnicodeString s ==>
      isCleanPalindrome_precond s ==>
      isCleanPalindrome_postcond s (isCleanPalindrome s)``;
