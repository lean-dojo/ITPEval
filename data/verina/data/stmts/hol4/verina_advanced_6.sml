(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_6,
  catalog title "allVowels": an executable case-insensitive Unicode-string
  test lowercases ASCII letters and checks that all five English vowels occur,
  together with its total correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val allVowels_validChar_def = new_definition (
  "allVowels_validChar_def",
  ``allVowels_validChar (c : num) <=>
      c < 55296 \/ (57343 < c /\ c < 1114112)``
);

val allVowels_string_def = new_definition (
  "allVowels_string_def",
  ``allVowels_string (s : num list) <=>
      EVERY allVowels_validChar s``
);

val toLower_def = new_definition (
  "toLower_def",
  ``toLower (c : num) =
      if 65 <= c /\ c <= 90 then c + 32 else c``
);

val normalize_str_def = new_definition (
  "normalize_str_def",
  ``normalize_str (s : num list) = MAP toLower s``
);

val allVowels_precond_def = new_definition (
  "allVowels_precond_def",
  ``allVowels_precond (s : num list) <=> T``
);

val allVowels_vowelSet_def = new_definition (
  "allVowels_vowelSet_def",
  ``allVowels_vowelSet = ([97; 101; 105; 111; 117] : num list)``
);

val allVowels_def = new_definition (
  "allVowels_def",
  ``allVowels (s : num list) =
      EVERY (\v : num. MEM v (normalize_str s)) allVowels_vowelSet``
);

val allVowels_postcond_def = new_definition (
  "allVowels_postcond_def",
  ``allVowels_postcond (s : num list) (result : bool) <=>
      (result <=>
       EVERY (\v : num. MEM v (normalize_str s)) allVowels_vowelSet)``
);

val allVowels_spec_satisfied =
  ``!s : num list.
      allVowels_string s ==>
      allVowels_precond s ==>
      allVowels_postcond s (allVowels s)``;
