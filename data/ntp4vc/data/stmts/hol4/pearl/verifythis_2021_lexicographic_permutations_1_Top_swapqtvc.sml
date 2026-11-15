(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_lexicographic_permutations_1_Top_swapqtvc:
  swapping two valid positions of an integer array exchanges their entries,
  preserves every other entry, and preserves the represented permutation.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val ntp4vc_lexperm_swap_index_def = Define `
  ntp4vc_lexperm_swap_index (i : int) =
    if i < (0 : int) then 0 else Num i`;

val ntp4vc_lexperm_swap_nth_def = Define `
  ntp4vc_lexperm_swap_nth (a : int list) (i : int) =
    if i < (0 : int) then (0 : int)
    else if ntp4vc_lexperm_swap_index i < LENGTH a
         then EL (ntp4vc_lexperm_swap_index i) a
         else (0 : int)`;

val ntp4vc_lexperm_swap_set_def = Define `
  ntp4vc_lexperm_swap_set
    (a : int list) (n : num) (x : int) =
    LUPDATE x n a`;

val ntp4vc_lexperm_swap_update_def = Define `
  ntp4vc_lexperm_swap_update
    (f : int -> int) (i : int) (x : int) =
    \k : int. if k = i then x else f k`;

val ntp4vc_lexperm_swap_occ_all_def = Define `
  ntp4vc_lexperm_swap_occ_all (x : int) (s : int list) =
    &(LENGTH (FILTER (\y : int. y = x) s))`;

val ntp4vc_lexperm_swap_is_permutation_def = Define `
  ntp4vc_lexperm_swap_is_permutation
    (p : int list) (a : int list) <=>
    LENGTH p = LENGTH a /\
    (!x : int.
       ntp4vc_lexperm_swap_occ_all x p =
       ntp4vc_lexperm_swap_occ_all x a)`;

val ntp4vc_lexperm_swap_to_seq_def = Define `
  ntp4vc_lexperm_swap_to_seq (a : int list) = a`;

val verifythis_2021_lexicographic_permutations_1_Top_swapqtvc_statement =
  ``!i : int.
    !a : int list.
    !j : int.
      (0 : int) <= i
      ==>
      i < &(LENGTH a)
      ==>
      (0 : int) <= j
      ==>
      j < &(LENGTH a)
      ==>
      ((0 : int) <= i /\
       i < &(LENGTH a) /\
       (let temp = ntp4vc_lexperm_swap_nth a i in
        ((0 : int) <= j /\ j < &(LENGTH a)) /\
        (let o1 = ntp4vc_lexperm_swap_nth a j in
         ((0 : int) <= i /\ i < &(LENGTH a)) /\
         (let after_i =
            ntp4vc_lexperm_swap_set
              a (ntp4vc_lexperm_swap_index i) o1 in
          LENGTH after_i = LENGTH a
          ==>
          (\k : int. ntp4vc_lexperm_swap_nth after_i k) =
            ntp4vc_lexperm_swap_update
              (\k : int. ntp4vc_lexperm_swap_nth a k) i o1
          ==>
          ((0 : int) <= j /\ j < &(LENGTH after_i)) /\
          (let swapped =
             ntp4vc_lexperm_swap_set
               after_i (ntp4vc_lexperm_swap_index j) temp in
           LENGTH swapped = LENGTH after_i
           ==>
           (\k : int. ntp4vc_lexperm_swap_nth swapped k) =
             ntp4vc_lexperm_swap_update
               (\k : int. ntp4vc_lexperm_swap_nth after_i k) j temp
           ==>
           ntp4vc_lexperm_swap_nth swapped i =
             ntp4vc_lexperm_swap_nth a j /\
           ntp4vc_lexperm_swap_nth swapped j =
             ntp4vc_lexperm_swap_nth a i /\
           (!k : int.
              (0 : int) <= k /\ k < &(LENGTH swapped)
              ==> ~(k = i)
              ==> ~(k = j)
              ==> ntp4vc_lexperm_swap_nth swapped k =
                  ntp4vc_lexperm_swap_nth a k) /\
           ntp4vc_lexperm_swap_is_permutation
             (ntp4vc_lexperm_swap_to_seq swapped)
             (ntp4vc_lexperm_swap_to_seq a))))))``;
