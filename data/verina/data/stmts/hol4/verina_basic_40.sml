(*
  Statement-only formalization of VERINA corpus artifact verina_basic_40,
  catalog title "secondSmallest": the executable indexed scan returns the
  second-smallest distinct value of an integer array under the stated
  nontriviality precondition and satisfies its attained-value ordering
  contract. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory;

val secondSmallest_nthD_def = Define `
  (secondSmallest_nthD
      (index : num) ([] : int list) = (0 : int)) /\
  (secondSmallest_nthD
      0 (x::xs) = x) /\
  (secondSmallest_nthD
      (SUC index) (x::xs) =
     secondSmallest_nthD index xs)
`;

val secondSmallest_precond_def = new_definition (
  "secondSmallest_precond_def",
  ``secondSmallest_precond (s : int list) <=>
      LENGTH s > 1 /\
      ?i j : num.
        i < LENGTH s /\
        j < LENGTH s /\
        secondSmallest_nthD i s <> secondSmallest_nthD j s``
);

val secondSmallestAuxFuel_def = Define `
  (secondSmallestAuxFuel
      (s : int list)
      (i : num)
      (minIdx : num)
      (secondIdx : num option)
      0 =
     case secondIdx of
       NONE => (0 : int)
     | SOME si => secondSmallest_nthD si s) /\
  (secondSmallestAuxFuel
      s i minIdx secondIdx (SUC fuel) =
     if LENGTH s <= i then
       case secondIdx of
         NONE => (0 : int)
       | SOME si => secondSmallest_nthD si s
     else
       let x = secondSmallest_nthD i s in
       let m = secondSmallest_nthD minIdx s in
         case secondIdx of
           NONE =>
             if x < m then
               secondSmallestAuxFuel
                 s (i + 1) i (SOME minIdx) fuel
             else if x > m then
               secondSmallestAuxFuel
                 s (i + 1) minIdx (SOME i) fuel
             else
               secondSmallestAuxFuel
                 s (i + 1) minIdx NONE fuel
         | SOME si =>
             let smin = secondSmallest_nthD si s in
               if x < m then
                 secondSmallestAuxFuel
                   s (i + 1) i (SOME minIdx) fuel
               else if x < smin /\ x > m then
                 secondSmallestAuxFuel
                   s (i + 1) minIdx (SOME i) fuel
               else
                 secondSmallestAuxFuel
                   s (i + 1) minIdx (SOME si) fuel)
`;

val secondSmallestAux_def = new_definition (
  "secondSmallestAux_def",
  ``secondSmallestAux
      (s : int list)
      (i : num)
      (minIdx : num)
      (secondIdx : num option) =
      secondSmallestAuxFuel
        s i minIdx secondIdx (LENGTH s - i)``
);

val secondSmallest_def = new_definition (
  "secondSmallest_def",
  ``secondSmallest (s : int list) =
      secondSmallestAux s 1 0 NONE``
);

val secondSmallest_postcond_def = new_definition (
  "secondSmallest_postcond_def",
  ``secondSmallest_postcond
      (s : int list) (result : int) <=>
      (?i : num.
         i < LENGTH s /\
         secondSmallest_nthD i s = result) /\
      (?j : num.
         j < LENGTH s /\
         secondSmallest_nthD j s < result /\
         !k : num.
           k < LENGTH s ==>
           secondSmallest_nthD k s <> secondSmallest_nthD j s ==>
           secondSmallest_nthD k s >= result)``
);

val secondSmallest_spec_satisfied =
  ``!s : int list.
      secondSmallest_precond s ==>
      secondSmallest_postcond s (secondSmallest s)``;
