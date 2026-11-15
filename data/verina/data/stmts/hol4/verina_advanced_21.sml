(*
  Statement-only formalization of VERINA artifact verina_advanced_21,
  cataloged as "isPalindrome": the executable Boolean program checks a
  Unicode-scalar string by both mirrored indices and accumulator reversal.
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

val isPalindrome_precond_def = new_definition (
  "isPalindrome_precond_def",
  ``isPalindrome_precond (s : num list) <=> T``
);

val checkIndicesFuel_def = Define `
  (checkIndicesFuel
      0 (left : num) (right : num) (chars : num list) = F) /\
  (checkIndicesFuel (SUC fuel) left right chars =
     if left >= right then
       T
     else
       case LLOOKUP chars left of
         NONE => F
       | SOME cLeft =>
           case LLOOKUP chars right of
             NONE => F
           | SOME cRight =>
               if cLeft = cRight then
                 checkIndicesFuel fuel (left + 1) (right - 1) chars
               else
                 F)
`;

val checkIndices_def = new_definition (
  "checkIndices_def",
  ``checkIndices (left : num) (right : num) (chars : num list) =
      checkIndicesFuel (SUC right) left right chars``
);

val reverseList_def = Define `
  (reverseList (acc : num list) ([] : num list) = acc) /\
  (reverseList acc (h::t) = reverseList (h::acc) t)
`;

val isPalindrome_def = new_definition (
  "isPalindrome_def",
  ``isPalindrome (s : num list) =
      let length = LENGTH s
      in
        if length <= 1 then
          T
        else
          let arr = s in
          let approach1 = checkIndices 0 (length - 1) arr in
          let reversed = reverseList [] arr in
          let approach2 = (arr = reversed)
          in
            approach1 /\ approach2``
);

val isPalindrome_postcond_def = new_definition (
  "isPalindrome_postcond_def",
  ``isPalindrome_postcond (s : num list) (result : bool) <=>
      (result ==> s = REVERSE s) /\
      (~result ==> s <> [] /\ s <> REVERSE s)``
);

val isPalindrome_spec_satisfied =
  ``!s : num list.
      isUnicodeString s ==>
      isPalindrome_precond s ==>
      isPalindrome_postcond s (isPalindrome s)``;
