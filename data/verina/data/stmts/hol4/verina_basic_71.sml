(*
  Statement-only formalization of VERINA corpus artifact verina_basic_71,
  catalog title "LongestCommonPrefix": the executable Unicode-character-list
  program scans two inputs from the left and returns their longest common
  prefix under its complete maximal-prefix contract. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory;

val LongestCommonPrefix_isUnicodeScalar_def = new_definition (
  "LongestCommonPrefix_isUnicodeScalar_def",
  ``LongestCommonPrefix_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val LongestCommonPrefix_isUnicodeString_def = new_definition (
  "LongestCommonPrefix_isUnicodeString_def",
  ``LongestCommonPrefix_isUnicodeString (s : num list) <=>
      EVERY LongestCommonPrefix_isUnicodeScalar s``
);

val LongestCommonPrefix_precond_def = new_definition (
  "LongestCommonPrefix_precond_def",
  ``LongestCommonPrefix_precond
      (str1 : num list) (str2 : num list) <=>
      T``
);

val LongestCommonPrefix_minLength_def = new_definition (
  "LongestCommonPrefix_minLength_def",
  ``LongestCommonPrefix_minLength
      (str1 : num list) (str2 : num list) =
      if LENGTH str1 <= LENGTH str2 then
        LENGTH str1
      else
        LENGTH str2``
);

val LongestCommonPrefix_getOpt_def = new_definition (
  "LongestCommonPrefix_getOpt_def",
  ``LongestCommonPrefix_getOpt
      (xs : num list) (idx : num) =
      if idx < LENGTH xs then
        SOME (EL idx xs)
      else
        NONE``
);

val LongestCommonPrefix_auxFuel_def = Define `
  (LongestCommonPrefix_auxFuel
      0
      (str1 : num list)
      (str2 : num list)
      (minLength : num)
      (idx : num)
      (acc : num list) =
     acc) /\
  (LongestCommonPrefix_auxFuel
      (SUC fuel)
      str1
      str2
      minLength
      idx
      acc =
     if idx < minLength then
       case LongestCommonPrefix_getOpt str1 idx of
         NONE => acc
       | SOME c1 =>
           (case LongestCommonPrefix_getOpt str2 idx of
              NONE => acc
            | SOME c2 =>
                if c1 <> c2 then
                  acc
                else
                  LongestCommonPrefix_auxFuel
                    fuel
                    str1
                    str2
                    minLength
                    (idx + 1)
                    (acc ++ [c1]))
     else
       acc)
`;

val LongestCommonPrefix_aux_def = new_definition (
  "LongestCommonPrefix_aux_def",
  ``LongestCommonPrefix_aux
      (str1 : num list)
      (str2 : num list)
      (minLength : num)
      (idx : num)
      (acc : num list) =
      LongestCommonPrefix_auxFuel
        (SUC (minLength - idx))
        str1
        str2
        minLength
        idx
        acc``
);

val LongestCommonPrefix_def = new_definition (
  "LongestCommonPrefix_def",
  ``LongestCommonPrefix
      (str1 : num list) (str2 : num list) =
      let minLength =
        LongestCommonPrefix_minLength str1 str2
      in
        LongestCommonPrefix_aux
          str1 str2 minLength 0 []``
);

val LongestCommonPrefix_postcond_def = new_definition (
  "LongestCommonPrefix_postcond_def",
  ``LongestCommonPrefix_postcond
      (str1 : num list)
      (str2 : num list)
      (result : num list) <=>
      LENGTH result <= LENGTH str1 /\
      result = TAKE (LENGTH result) str1 /\
      LENGTH result <= LENGTH str2 /\
      result = TAKE (LENGTH result) str2 /\
      (LENGTH result = LENGTH str1 \/
       LENGTH result = LENGTH str2 \/
       LongestCommonPrefix_getOpt str1 (LENGTH result) <>
       LongestCommonPrefix_getOpt str2 (LENGTH result))``
);

val LongestCommonPrefix_spec_satisfied =
  ``!(str1 : num list) (str2 : num list).
      LongestCommonPrefix_isUnicodeString str1 ==>
      LongestCommonPrefix_isUnicodeString str2 ==>
      LongestCommonPrefix_precond str1 str2 ==>
      LongestCommonPrefix_postcond
        str1 str2 (LongestCommonPrefix str1 str2)``;
