(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_pair_insertion_sort_Challenge1_pair_insertion_sortqtvc:
  the verification condition for pair insertion sort, including the outer
  sorted-prefix invariant, the two nested insertion loops, list updates, and
  permutation preservation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory sortingTheory;

val pair_sort_to_num_def = Define `
  pair_sort_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val pair_sort_get_def = Define `
  pair_sort_get (xs : int list) (z : int) =
    if z < (0 : int) then
      (0 : int)
    else if pair_sort_to_num z < LENGTH xs then
      EL (pair_sort_to_num z) xs
    else
      (0 : int)`;

val pair_sort_set_def = Define `
  pair_sort_set (xs : int list) (z : int) (value : int) =
    LUPDATE value (pair_sort_to_num z) xs`;

val pair_sort_update_matches_def = Define `
  pair_sort_update_matches
      (xs : int list) (z : int) (value : int) <=>
    LENGTH (pair_sort_set xs z value) = LENGTH xs /\
    (\k : int. pair_sort_get (pair_sort_set xs z value) k) =
      (\k : int. if k = z then value else pair_sort_get xs k)`;

val pair_sort_sorted_before_def = Define `
  pair_sort_sorted_before (xs : int list) (upper : int) <=>
    !k l : int.
      (0 : int) <= k /\ k <= l /\ l < upper ==>
      pair_sort_get xs k <= pair_sort_get xs l`;

val pair_sort_sorted_through_def = Define `
  pair_sort_sorted_through (xs : int list) (last : int) <=>
    !k l : int.
      (0 : int) <= k /\ k <= l /\ l <= last ==>
      pair_sort_get xs k <= pair_sort_get xs l`;

val pair_sort_outer_inv_def = Define `
  pair_sort_outer_inv
      (original : int list) (i : int) (xs : int list) <=>
    ((0 : int) <= i /\ i <= &(LENGTH xs)) /\
    pair_sort_sorted_before xs i /\
    PERM original xs`;

val pair_sort_first_inv_def = Define `
  pair_sort_first_inv
      (original : int list) (i : int) (x : int) (y : int)
      (j : int) (xs : int list) <=>
    ((0 : int) - 1 <= j /\ j < i) /\
    pair_sort_sorted_through xs j /\
    (!k l : int.
       (0 : int) <= k /\ k <= j /\
       j + (2 : int) < l /\ l < i + (2 : int) ==>
       pair_sort_get xs k <= pair_sort_get xs l) /\
    (!k l : int.
       j + (2 : int) < k /\ k <= l /\ l < i + (2 : int) ==>
       pair_sort_get xs k <= pair_sort_get xs l) /\
    (!l : int.
       j + (2 : int) < l /\ l < i + (2 : int) ==>
       x < pair_sort_get xs l) /\
    PERM original
      (pair_sort_set
        (pair_sort_set xs (j + (1 : int)) y)
        (j + (2 : int))
        x)`;

val pair_sort_second_inv_def = Define `
  pair_sort_second_inv
      (original : int list) (i : int) (y : int)
      (j : int) (xs : int list) <=>
    ((0 : int) - 1 <= j /\ j < i) /\
    pair_sort_sorted_through xs j /\
    (!k l : int.
       (0 : int) <= k /\ k <= j /\
       j + (1 : int) < l /\ l < i + (2 : int) ==>
       pair_sort_get xs k <= pair_sort_get xs l) /\
    (!k l : int.
       j + (1 : int) < k /\ k <= l /\ l < i + (2 : int) ==>
       pair_sort_get xs k <= pair_sort_get xs l) /\
    (!l : int.
       j + (1 : int) < l /\ l < i + (2 : int) ==>
       y <= pair_sort_get xs l) /\
    PERM original (pair_sort_set xs (j + (1 : int)) y)`;

val pair_sort_second_phase_def = Define `
  pair_sort_second_phase
      (original : int list) (base : int list)
      (i : int) (y : int) (start : int list) <=>
    !j : int. !xs : int list.
      LENGTH xs = LENGTH start ==>
      pair_sort_second_inv original i y j xs ==>
      (((0 : int) <= j ==>
        (0 : int) <= j /\ j < &(LENGTH xs)) /\
       (!flag : bool.
          (if (0 : int) <= j then
             flag = (y < pair_sort_get xs j)
           else
             flag = F) ==>
          if flag then
            ((0 : int) <= j /\ j < &(LENGTH xs)) /\
            (let shifted_value = pair_sort_get xs j in
             let shifted_index = j + (1 : int) in
               ((0 : int) <= shifted_index /\
                shifted_index < &(LENGTH xs)) /\
               (let shifted =
                    pair_sort_set xs shifted_index shifted_value
                in
                  pair_sort_update_matches
                    xs shifted_index shifted_value ==>
                  ((0 : int) <= j /\ j - (1 : int) < j) /\
                  pair_sort_second_inv
                    original i y (j - (1 : int)) shifted))
          else
            let insertion_index = j + (1 : int) in
              ((0 : int) <= insertion_index /\
               insertion_index < &(LENGTH xs)) /\
              (let finished =
                   pair_sort_set xs insertion_index y
               in
                 pair_sort_update_matches xs insertion_index y ==>
                 (((0 : int) <= &(LENGTH base) - i /\
                    &(LENGTH finished) - (i + (2 : int)) <
                      &(LENGTH base) - i) /\
                  pair_sort_outer_inv
                    original (i + (2 : int)) finished))))`;

val pair_sort_first_phase_def = Define `
  pair_sort_first_phase
      (original : int list) (base : int list)
      (i : int) (x : int) (y : int) (start : int list) <=>
    pair_sort_first_inv
      original i x y (i - (1 : int)) start /\
    !j : int. !xs : int list.
      LENGTH xs = LENGTH start ==>
      pair_sort_first_inv original i x y j xs ==>
      (((0 : int) <= j ==>
        (0 : int) <= j /\ j < &(LENGTH xs)) /\
       (!flag : bool.
          (if (0 : int) <= j then
             flag = (x < pair_sort_get xs j)
           else
             flag = F) ==>
          if flag then
            ((0 : int) <= j /\ j < &(LENGTH xs)) /\
            (let shifted_value = pair_sort_get xs j in
             let shifted_index = j + (2 : int) in
               ((0 : int) <= shifted_index /\
                shifted_index < &(LENGTH xs)) /\
               (let shifted =
                    pair_sort_set xs shifted_index shifted_value
                in
                  pair_sort_update_matches
                    xs shifted_index shifted_value ==>
                  ((0 : int) <= j /\ j - (1 : int) < j) /\
                  pair_sort_first_inv
                    original i x y (j - (1 : int)) shifted))
          else
            let insertion_index = j + (2 : int) in
              ((0 : int) <= insertion_index /\
               insertion_index < &(LENGTH xs)) /\
              (let inserted =
                   pair_sort_set xs insertion_index x
               in
                 pair_sort_update_matches xs insertion_index x ==>
                 pair_sort_second_inv original i y j inserted /\
                 pair_sort_second_phase
                   original base i y inserted)))`;

val pair_sort_single_inv_def = Define `
  pair_sort_single_inv
      (original : int list) (i : int) (y : int)
      (j : int) (xs : int list) <=>
    ((0 : int) - 1 <= j /\ j < i) /\
    pair_sort_sorted_through xs j /\
    (!k l : int.
       (0 : int) <= k /\ k <= j /\
       j + (1 : int) < l /\ l < &(LENGTH xs) ==>
       pair_sort_get xs k <= pair_sort_get xs l) /\
    (!k l : int.
       j + (1 : int) < k /\ k <= l /\ l < &(LENGTH xs) ==>
       pair_sort_get xs k <= pair_sort_get xs l) /\
    (!l : int.
       j + (1 : int) < l /\ l < &(LENGTH xs) ==>
       y < pair_sort_get xs l) /\
    PERM original (pair_sort_set xs (j + (1 : int)) y)`;

val pair_sort_single_phase_def = Define `
  pair_sort_single_phase
      (original : int list) (i : int) (y : int)
      (start : int list) <=>
    pair_sort_single_inv
      original i y (i - (1 : int)) start /\
    !j : int. !xs : int list.
      LENGTH xs = LENGTH start ==>
      pair_sort_single_inv original i y j xs ==>
      (((0 : int) <= j ==>
        (0 : int) <= j /\ j < &(LENGTH xs)) /\
       (!flag : bool.
          (if (0 : int) <= j then
             flag = (y < pair_sort_get xs j)
           else
             flag = F) ==>
          if flag then
            ((0 : int) <= j /\ j < &(LENGTH xs)) /\
            (let shifted_value = pair_sort_get xs j in
             let shifted_index = j + (1 : int) in
               ((0 : int) <= shifted_index /\
                shifted_index < &(LENGTH xs)) /\
               (let shifted =
                    pair_sort_set xs shifted_index shifted_value
                in
                  pair_sort_update_matches
                    xs shifted_index shifted_value ==>
                  ((0 : int) <= j /\ j - (1 : int) < j) /\
                  pair_sort_single_inv
                    original i y (j - (1 : int)) shifted))
          else
            let insertion_index = j + (1 : int) in
              ((0 : int) <= insertion_index /\
               insertion_index < &(LENGTH xs)) /\
              (let finished =
                   pair_sort_set xs insertion_index y
               in
                 pair_sort_update_matches xs insertion_index y ==>
                 pair_sort_sorted_before
                   finished (&(LENGTH finished)) /\
                 PERM original finished)))`;

val verifythis_2017_pair_insertion_sort_Challenge1_pair_insertion_sortqtvc_statement =
  ``!a : int list.
      (0 : int) <= (0 : int) /\
      (0 : int) <= &(LENGTH a) /\
      pair_sort_sorted_before a (0 : int) /\
      PERM a a /\
      !i : int. !a1 : int list.
        LENGTH a1 = LENGTH a ==>
        pair_sort_outer_inv a i a1 ==>
        if i < &(LENGTH a1) - (1 : int) then
          ((0 : int) <= i /\ i < &(LENGTH a1)) /\
          (let first = pair_sort_get a1 i in
           let next_index = i + (1 : int) in
             ((0 : int) <= next_index /\
              next_index < &(LENGTH a1)) /\
             (let second = pair_sort_get a1 next_index in
                if first < second then
                  pair_sort_first_phase
                    a a1 i second first a1
                else
                  pair_sort_first_phase
                    a a1 i first second a1))
        else if i = &(LENGTH a1) - (1 : int) then
          ((0 : int) <= i /\ i < &(LENGTH a1)) /\
          (let y = pair_sort_get a1 i in
             pair_sort_single_phase a i y a1)
        else
          pair_sort_sorted_before a1 (&(LENGTH a1)) /\
          PERM a a1``;
