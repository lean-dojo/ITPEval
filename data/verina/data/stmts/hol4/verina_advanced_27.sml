(*
  Statement-only formalization of VERINA artifact verina_advanced_27,
  cataloged as "longestCommonSubsequence": the executable recursive program
  returns a longest common subsequence of two Unicode-scalar strings, choosing
  the left recursive result when lengths tie. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val longestCommonSubsequence_isUnicodeScalar_def = new_definition (
  "longestCommonSubsequence_isUnicodeScalar_def",
  ``longestCommonSubsequence_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val longestCommonSubsequence_isUnicodeString_def = new_definition (
  "longestCommonSubsequence_isUnicodeString_def",
  ``longestCommonSubsequence_isUnicodeString (s : num list) <=>
      EVERY longestCommonSubsequence_isUnicodeScalar s``
);

val longestCommonSubsequence_precond_def = new_definition (
  "longestCommonSubsequence_precond_def",
  ``longestCommonSubsequence_precond
      (s1 : num list) (s2 : num list) <=> T``
);

val toCharList_def = new_definition (
  "toCharList_def",
  ``toCharList (s : num list) = s``
);

val fromCharList_def = new_definition (
  "fromCharList_def",
  ``fromCharList (cs : num list) = cs``
);

val lcsAux_def = Define `
  (lcsAux ([] : num list) (ys : num list) = ([] : num list)) /\
  (lcsAux (x::xs) ([] : num list) = []) /\
  (lcsAux (x::xs) (y::ys) =
     if x = y then
       x::lcsAux xs ys
     else
       let left = lcsAux xs (y::ys) in
       let right = lcsAux (x::xs) ys
       in
         if LENGTH left >= LENGTH right then left else right)
`;

val longestCommonSubsequence_def = new_definition (
  "longestCommonSubsequence_def",
  ``longestCommonSubsequence (s1 : num list) (s2 : num list) =
      let xs = toCharList s1 in
      let ys = toCharList s2 in
      let resultList = lcsAux xs ys
      in
        fromCharList resultList``
);

val longestCommonSubsequence_allSubseq_def = new_definition (
  "longestCommonSubsequence_allSubseq_def",
  ``longestCommonSubsequence_allSubseq (arr : num list) =
      MAP REVERSE
        (FOLDL
          (\acc x. acc ++ MAP (\sub. x::sub) acc)
          ([[]] : num list list)
          arr)``
);

val longestCommonSubsequence_postcond_def = new_definition (
  "longestCommonSubsequence_postcond_def",
  ``longestCommonSubsequence_postcond
      (s1 : num list)
      (s2 : num list)
      (result : num list) <=>
      let subseqA = longestCommonSubsequence_allSubseq s1 in
      let subseqB = longestCommonSubsequence_allSubseq s2 in
      let commonSubseq =
        FILTER (\l : num list. MEM l subseqB) subseqA
      in
        MEM result commonSubseq /\
        EVERY (\l : num list. LENGTH l <= LENGTH result) commonSubseq``
);

val longestCommonSubsequence_spec_satisfied =
  ``!(s1 : num list) (s2 : num list).
      longestCommonSubsequence_isUnicodeString s1 ==>
      longestCommonSubsequence_isUnicodeString s2 ==>
      longestCommonSubsequence_precond s1 s2 ==>
      longestCommonSubsequence_postcond
        s1 s2 (longestCommonSubsequence s1 s2)``;
