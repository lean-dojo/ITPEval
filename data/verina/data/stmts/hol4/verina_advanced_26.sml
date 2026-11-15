(*
  Statement-only formalization of VERINA artifact verina_advanced_26,
  cataloged as "letterCombinations": the executable program generates the
  telephone-keypad letter combinations for a Unicode-scalar digit string,
  returning the empty list for empty or invalid input. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val letterCombinations_isUnicodeScalar_def = new_definition (
  "letterCombinations_isUnicodeScalar_def",
  ``letterCombinations_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val letterCombinations_isUnicodeString_def = new_definition (
  "letterCombinations_isUnicodeString_def",
  ``letterCombinations_isUnicodeString (s : num list) <=>
      EVERY letterCombinations_isUnicodeScalar s``
);

val digitToLetters_def = new_definition (
  "digitToLetters_def",
  ``digitToLetters (c : num) =
      if c = 50 then [97; 98; 99]
      else if c = 51 then [100; 101; 102]
      else if c = 52 then [103; 104; 105]
      else if c = 53 then [106; 107; 108]
      else if c = 54 then [109; 110; 111]
      else if c = 55 then [112; 113; 114; 115]
      else if c = 56 then [116; 117; 118]
      else if c = 57 then [119; 120; 121; 122]
      else []``
);

val letterCombinations_precond_def = new_definition (
  "letterCombinations_precond_def",
  ``letterCombinations_precond (digits : num list) <=> T``
);

val letterCombinations_go_def = Define `
  (letterCombinations_go ([] : num list) = ([] : num list list)) /\
  (letterCombinations_go (d::ds) =
     let restCombinations = letterCombinations_go ds in
     let currentLetters = digitToLetters d in
       if restCombinations = [] then
         MAP (\c. [c]) currentLetters
       else
         FLAT
           (MAP
             (\c. MAP (\s. c::s) restCombinations)
             currentLetters))
`;

val letterCombinations_def = new_definition (
  "letterCombinations_def",
  ``letterCombinations (digits : num list) =
      if EXISTS (\c. digitToLetters c = []) digits then
        []
      else
        letterCombinations_go digits``
);

val letterCombinations_expected_def = new_definition (
  "letterCombinations_expected_def",
  ``letterCombinations_expected (digits : num list) =
      FOLDL
        (\acc ls.
           FLAT
             (MAP
               (\s. MAP (\c. s ++ [c]) ls)
               acc))
        ([[]] : num list list)
        (MAP digitToLetters digits)``
);

val letterCombinations_postcond_def = new_definition (
  "letterCombinations_postcond_def",
  ``letterCombinations_postcond
      (digits : num list) (result : num list list) <=>
      if digits = [] then
        result = []
      else if
        EXISTS
          (\c. ~MEM c [50; 51; 52; 53; 54; 55; 56; 57])
          digits
      then
        result = []
      else
        let expected = letterCombinations_expected digits
        in
          LENGTH result = LENGTH expected /\
          EVERY (\s. MEM s expected) result /\
          EVERY (\s. MEM s result) expected``
);

val letterCombinations_spec_satisfied =
  ``!digits : num list.
      letterCombinations_isUnicodeString digits ==>
      letterCombinations_precond digits ==>
      letterCombinations_postcond
        digits
        (letterCombinations digits)``;
