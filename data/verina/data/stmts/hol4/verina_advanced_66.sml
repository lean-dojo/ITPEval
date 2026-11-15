(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_66,
  catalog title "reverseWords": the executable Unicode-string program splits
  on spaces, removes empty words, reverses their order, and rejoins them with
  single spaces under its correctness contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val reverseWords_isUnicodeScalar_def = new_definition (
  "reverseWords_isUnicodeScalar_def",
  ``reverseWords_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val reverseWords_isUnicodeString_def = new_definition (
  "reverseWords_isUnicodeString_def",
  ``reverseWords_isUnicodeString (s : num list) <=>
      EVERY reverseWords_isUnicodeScalar s``
);

val reverseWords_precond_def = new_definition (
  "reverseWords_precond_def",
  ``reverseWords_precond (words_str : num list) <=> T``
);

val reverseWords_splitOnSpaceAux_def = Define `
  (reverseWords_splitOnSpaceAux
      ([] : num list) (currentRev : num list) =
     [REVERSE currentRev]) /\
  (reverseWords_splitOnSpaceAux
      (c::cs) currentRev =
     if c = 32 then
       REVERSE currentRev::
         reverseWords_splitOnSpaceAux cs ([] : num list)
     else
       reverseWords_splitOnSpaceAux cs (c::currentRev))
`;

val reverseWords_splitOnSpace_def = new_definition (
  "reverseWords_splitOnSpace_def",
  ``reverseWords_splitOnSpace (words_str : num list) =
      reverseWords_splitOnSpaceAux words_str ([] : num list)``
);

val reverseWords_filterNonEmpty_def = Define `
  (reverseWords_filterNonEmpty
      ([] : num list list) = ([] : num list list)) /\
  (reverseWords_filterNonEmpty
      (word::words) =
     if word = [] then
       reverseWords_filterNonEmpty words
     else
       word::reverseWords_filterNonEmpty words)
`;

val reverseWords_joinWithSpace_def = Define `
  (reverseWords_joinWithSpace
      ([] : num list list) = ([] : num list)) /\
  (reverseWords_joinWithSpace
      (word::words) =
     if words = [] then
       word
     else
       word ++ (32::reverseWords_joinWithSpace words))
`;

val reverseWords_def = new_definition (
  "reverseWords_def",
  ``reverseWords (words_str : num list) =
      let rawWords = reverseWords_splitOnSpace words_str in
      let filteredWords = reverseWords_filterNonEmpty rawWords in
      let revWords = REVERSE filteredWords in
      let result = reverseWords_joinWithSpace revWords
      in
        result``
);

val reverseWords_intercalateSpace_def = Define `
  (reverseWords_intercalateSpace
      ([] : num list list) = ([] : num list)) /\
  (reverseWords_intercalateSpace
      (word::words) =
     if words = [] then
       word
     else
       word ++ (32::reverseWords_intercalateSpace words))
`;

val reverseWords_postcond_def = new_definition (
  "reverseWords_postcond_def",
  ``reverseWords_postcond
      (words_str : num list) (result : num list) <=>
      ?words : num list list.
        words =
          FILTER
            (\word : num list. ~(word = []))
            (reverseWords_splitOnSpace words_str) /\
        result =
          reverseWords_intercalateSpace (REVERSE words)``
);

val reverseWords_spec_satisfied =
  ``!words_str : num list.
      reverseWords_isUnicodeString words_str ==>
      reverseWords_precond words_str ==>
      reverseWords_postcond
        words_str
        (reverseWords words_str)``;
