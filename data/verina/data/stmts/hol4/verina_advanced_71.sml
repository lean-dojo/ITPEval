(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_71,
  catalog title "shortestBeautifulSubstring": the executable program selects
  the shortest nonempty contiguous substring of a binary string containing
  exactly k ones, breaking equal-length ties lexicographically and returning
  the empty string when none exists. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory optionTheory;

val shortestBeautifulSubstring_countOnes_def = Define `
  (shortestBeautifulSubstring_countOnes ([] : num list) = 0) /\
  (shortestBeautifulSubstring_countOnes (c::cs) =
     (if c = 49 then 1 else 0) +
     shortestBeautifulSubstring_countOnes cs)
`;

val shortestBeautifulSubstring_precond_def = new_definition (
  "shortestBeautifulSubstring_precond_def",
  ``shortestBeautifulSubstring_precond
      (s : num list) (k : num) <=>
      EVERY (\c : num. c = 48 \/ c = 49) s``
);

val shortestBeautifulSubstring_lexLt_def = Define `
  (shortestBeautifulSubstring_lexLt
      ([] : num list) ([] : num list) = F) /\
  (shortestBeautifulSubstring_lexLt
      ([] : num list) (y::ys) = T) /\
  (shortestBeautifulSubstring_lexLt
      (x::xs) ([] : num list) = F) /\
  (shortestBeautifulSubstring_lexLt
      (x::xs) (y::ys) =
     if x < y then
       T
     else if x = y then
       shortestBeautifulSubstring_lexLt xs ys
     else
       F)
`;

val shortestBeautifulSubstring_lexLe_def = Define `
  (shortestBeautifulSubstring_lexLe
      ([] : num list) (ys : num list) = T) /\
  (shortestBeautifulSubstring_lexLe
      (x::xs) ([] : num list) = F) /\
  (shortestBeautifulSubstring_lexLe
      (x::xs) (y::ys) =
     if x < y then
       T
     else if x = y then
       shortestBeautifulSubstring_lexLe xs ys
     else
       F)
`;

val shortestBeautifulSubstring_listToString_def = new_definition (
  "shortestBeautifulSubstring_listToString_def",
  ``shortestBeautifulSubstring_listToString (lst : num list) = lst``
);

val shortestBeautifulSubstring_isLexSmaller_def = new_definition (
  "shortestBeautifulSubstring_isLexSmaller_def",
  ``shortestBeautifulSubstring_isLexSmaller
      (a : num list) (b : num list) <=>
      shortestBeautifulSubstring_lexLt
        (shortestBeautifulSubstring_listToString a)
        (shortestBeautifulSubstring_listToString b)``
);

val shortestBeautifulSubstring_allSubstrings_def = new_definition (
  "shortestBeautifulSubstring_allSubstrings_def",
  ``shortestBeautifulSubstring_allSubstrings (s : num list) =
      FLAT
        (MAP
          (\i : num.
            MAP
              (\j : num. TAKE (j + 1) (DROP i s))
              (COUNT_LIST (LENGTH s - i)))
          (COUNT_LIST (LENGTH s)))``
);

val shortestBeautifulSubstring_compare_def = new_definition (
  "shortestBeautifulSubstring_compare_def",
  ``shortestBeautifulSubstring_compare
      (a : num list) (b : num list) <=>
      LENGTH a < LENGTH b \/
      (LENGTH a = LENGTH b /\
       shortestBeautifulSubstring_isLexSmaller a b)``
);

val shortestBeautifulSubstring_step_def = new_definition (
  "shortestBeautifulSubstring_step_def",
  ``shortestBeautifulSubstring_step
      (acc : num list option) (cur : num list) =
      case acc of
        NONE => SOME cur
      | SOME best =>
          if shortestBeautifulSubstring_compare cur best then
            SOME cur
          else
            SOME best``
);

val shortestBeautifulSubstring_def = new_definition (
  "shortestBeautifulSubstring_def",
  ``shortestBeautifulSubstring (s : num list) (k : num) =
      let chars = s in
      let candidates =
        FILTER
          (\sub : num list.
            shortestBeautifulSubstring_countOnes sub = k)
          (shortestBeautifulSubstring_allSubstrings chars)
      in
      let best =
        FOLDL
          shortestBeautifulSubstring_step
          (NONE : num list option)
          candidates
      in
        case best of
          NONE => ([] : num list)
        | SOME b => b``
);

val shortestBeautifulSubstring_specSubstrings_def = new_definition (
  "shortestBeautifulSubstring_specSubstrings_def",
  ``shortestBeautifulSubstring_specSubstrings (s : num list) =
      FLAT
        (MAP
          (\i : num.
            MAP
              (\len : num. TAKE len (DROP i s))
              (COUNT_LIST (LENGTH s - i + 1)))
          (COUNT_LIST (LENGTH s)))``
);

val shortestBeautifulSubstring_targets_def = new_definition (
  "shortestBeautifulSubstring_targets_def",
  ``shortestBeautifulSubstring_targets
      (s : num list) (k : num) =
      let substrings =
        shortestBeautifulSubstring_specSubstrings s
      in
      let beautiful =
        FILTER
          (\sub : num list.
            shortestBeautifulSubstring_countOnes sub = k)
          substrings
      in
        FILTER
          (\str : num list. str <> [])
          (MAP shortestBeautifulSubstring_listToString beautiful)``
);

val shortestBeautifulSubstring_postcond_def = new_definition (
  "shortestBeautifulSubstring_postcond_def",
  ``shortestBeautifulSubstring_postcond
      (s : num list)
      (k : num)
      (result : num list) <=>
      let targets = shortestBeautifulSubstring_targets s k in
        (result = [] /\ targets = []) \/
        (MEM result targets /\
         EVERY
           (\r : num list.
             LENGTH result < LENGTH r \/
             (LENGTH r = LENGTH result /\
              shortestBeautifulSubstring_lexLe result r))
           targets)``
);

val shortestBeautifulSubstring_spec_satisfied =
  ``!(s : num list) (k : num).
      shortestBeautifulSubstring_precond s k ==>
      shortestBeautifulSubstring_postcond
        s k (shortestBeautifulSubstring s k)``;
