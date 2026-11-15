(*
  Statement-only formalization of VERINA artifact verina_advanced_37,
  cataloged as "majorityElement": insertion-sorting an integer list and
  returning its middle element yields the guaranteed majority element and
  satisfies the stated occurrence-count contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val majorityElement_count_def = new_definition (
  "majorityElement_count_def",
  ``majorityElement_count (x : int) (nums : int list) =
      LENGTH (FILTER (\y : int. y = x) nums)``
);

val majorityElement_precond_def = new_definition (
  "majorityElement_precond_def",
  ``majorityElement_precond (nums : int list) <=>
      LENGTH nums > 0 /\
      EXISTS
        (\x : int.
          majorityElement_count x nums > LENGTH nums DIV 2)
        nums``
);

val majorityElement_insert_def = Define `
  (majorityElement_insert (x : int) ([] : int list) = [x]) /\
  (majorityElement_insert x (h::t) =
     if x <= h then
       x::h::t
     else
       h::majorityElement_insert x t)
`;

val majorityElement_insertionSort_def = Define `
  (majorityElement_insertionSort ([] : int list) = ([] : int list)) /\
  (majorityElement_insertionSort (h::t) =
     majorityElement_insert h (majorityElement_insertionSort t))
`;

val majorityElement_getAt_def = new_definition (
  "majorityElement_getAt_def",
  ``majorityElement_getAt (xs : int list) (i : num) =
      case DROP i xs of
        [] => (0 : int)
      | h::t => h``
);

val majorityElement_def = new_definition (
  "majorityElement_def",
  ``majorityElement (nums : int list) =
      let sorted = majorityElement_insertionSort nums
      in
        majorityElement_getAt sorted (LENGTH sorted DIV 2)``
);

val majorityElement_postcond_def = new_definition (
  "majorityElement_postcond_def",
  ``majorityElement_postcond
      (nums : int list) (result : int) <=>
      let n = LENGTH nums
      in
        majorityElement_count result nums > n DIV 2 /\
        EVERY
          (\x : int.
            x = result \/ majorityElement_count x nums <= n DIV 2)
          nums``
);

val majorityElement_spec_satisfied =
  ``!nums : int list.
      majorityElement_precond nums ==>
      majorityElement_postcond nums (majorityElement nums)``;
