(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_all_columnsqtvc: the
  verification condition for sorting every column of an integer matrix,
  either directly or by transpose, row sorting, and transpose back, while
  preserving each column's multiset. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val _ = type_abbrev
  ("sac_matrix", ``:int # (int # (int -> int -> int))``);

val sac_to_num_def = Define `
  sac_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sac_rows_def = Define `
  sac_rows (m : sac_matrix) = FST m`;

val sac_columns_def = Define `
  sac_columns (m : sac_matrix) = FST (SND m)`;

val sac_elts_def = Define `
  sac_elts (m : sac_matrix) = SND (SND m)`;

val sac_matrix_ok_def = Define `
  sac_matrix_ok (m : sac_matrix) <=>
    (0 : int) <= sac_rows m /\ (0 : int) <= sac_columns m`;

val sac_dimensions_def = Define `
  sac_dimensions (current : sac_matrix) (previous : sac_matrix) <=>
    sac_rows current = sac_rows previous /\
    sac_columns current = sac_columns previous`;

val sac_column_def = Define `
  sac_column (m : sac_matrix) (j : int) =
    \i : int. sac_elts m i j`;

val sac_occurrences_def = Define `
  sac_occurrences
      (value : int)
      (f : int -> int)
      (lower : int)
      (upper : int) =
    &(LENGTH
        (FILTER
          (\index : int. f index = value)
          (GENLIST
            (\offset : num. lower + &offset)
            (sac_to_num (upper - lower)))))`;

val sac_map_permut_def = Define `
  sac_map_permut
      (first_map : int -> int)
      (second_map : int -> int)
      (lower : int)
      (upper : int) <=>
    !value : int.
      sac_occurrences value first_map lower upper =
      sac_occurrences value second_map lower upper`;

val sac_columns_permuted_def = Define `
  sac_columns_permuted
      (current : sac_matrix)
      (original : sac_matrix) <=>
    !j : int.
      ((0 : int) <= j /\ j < sac_columns current) ==>
      sac_map_permut
        (sac_column current j)
        (sac_column original j)
        (0 : int)
        (sac_rows current)`;

val sac_columns_sorted_prefix_def = Define `
  sac_columns_sorted_prefix
      (current : sac_matrix)
      (limit : int) <=>
    !i j k : int.
      (((0 : int) <= i /\ i <= k /\ k < sac_rows current) /\
       ((0 : int) <= j /\ j < limit)) ==>
      sac_elts current i j <= sac_elts current k j`;

val sac_columns_sorted_def = Define `
  sac_columns_sorted (current : sac_matrix) <=>
    sac_columns_sorted_prefix current (sac_columns current)`;

val sac_final_columns_def = Define `
  sac_final_columns
      (current : sac_matrix)
      (original : sac_matrix) <=>
    sac_columns_permuted current original /\
    sac_columns_sorted current`;

val sac_unchanged_except_column_def = Define `
  sac_unchanged_except_column
      (current : sac_matrix)
      (previous : sac_matrix)
      (tid : int) <=>
    !i k : int.
      (((0 : int) <= i /\ i < sac_rows current) /\
       ((0 : int) <= k /\ k < sac_columns current) /\
       ~(k = tid)) ==>
      sac_elts current i k = sac_elts previous i k`;

val sac_column_sorted_at_def = Define `
  sac_column_sorted_at
      (current : sac_matrix)
      (tid : int) <=>
    !i k : int.
      ((0 : int) <= i /\ i <= k /\ k < sac_rows current) ==>
      sac_elts current i tid <= sac_elts current k tid`;

val sac_column_permuted_at_def = Define `
  sac_column_permuted_at
      (current : sac_matrix)
      (previous : sac_matrix)
      (tid : int) <=>
    sac_map_permut
      (sac_column current tid)
      (sac_column previous tid)
      (0 : int)
      (sac_rows current)`;

val sac_direct_step_vc_def = Define `
  sac_direct_step_vc
      (original : sac_matrix)
      (current : sac_matrix)
      (last : int) <=>
    !tid : int.
      (((0 : int) <= tid /\ tid <= last) /\
       sac_columns_permuted current original /\
       sac_columns_sorted_prefix current tid) ==>
      (((0 : int) <= tid /\ tid < sac_columns current) /\
       (!next : sac_matrix.
          sac_matrix_ok next ==>
          sac_dimensions next current ==>
          (sac_unchanged_except_column next current tid /\
           sac_column_sorted_at next tid /\
           sac_column_permuted_at next current tid) ==>
          (sac_columns_permuted next original /\
           sac_columns_sorted_prefix
             next (tid + (1 : int)))))`;

val sac_direct_run_vc_def = Define `
  sac_direct_run_vc
      (original : sac_matrix)
      (current : sac_matrix)
      (last : int) <=>
    sac_direct_step_vc original current last /\
    ((sac_columns_permuted current original /\
      sac_columns_sorted_prefix current (last + (1 : int))) ==>
     sac_final_columns current original)`;

val sac_direct_branch_vc_def = Define `
  sac_direct_branch_vc (original : sac_matrix) <=>
    let last = sac_columns original - (1 : int) in
      (((0 : int) <= last + (1 : int) ==>
        ((sac_columns_permuted original original /\
          sac_columns_sorted_prefix original (0 : int)) /\
         (!current : sac_matrix.
            sac_matrix_ok current ==>
            sac_dimensions current original ==>
            sac_direct_run_vc original current last))) /\
       (last + (1 : int) < (0 : int) ==>
        sac_final_columns original original))`;

val sac_transpose_relation_def = Define `
  sac_transpose_relation
      (before : sac_matrix)
      (after : sac_matrix) <=>
    !i j : int.
      (((0 : int) <= i /\ i < sac_rows after) /\
       ((0 : int) <= j /\ j < sac_columns after)) ==>
      sac_elts before i j = sac_elts after j i`;

val sac_rows_permuted_from_columns_def = Define `
  sac_rows_permuted_from_columns
      (current : sac_matrix)
      (original : sac_matrix)
      (n : int) <=>
    !j : int.
      ((0 : int) <= j /\ j < n) ==>
      sac_map_permut
        (sac_elts current j)
        (sac_column original j)
        (0 : int)
        n`;

val sac_rows_sorted_prefix_def = Define `
  sac_rows_sorted_prefix
      (current : sac_matrix)
      (n : int)
      (limit : int) <=>
    !i j k : int.
      (((0 : int) <= i /\ i <= k /\ k < n) /\
       ((0 : int) <= j /\ j < limit)) ==>
      sac_elts current j i <= sac_elts current j k`;

val sac_unchanged_except_row_def = Define `
  sac_unchanged_except_row
      (current : sac_matrix)
      (previous : sac_matrix)
      (tid : int) <=>
    !j k : int.
      (((0 : int) <= j /\ j < sac_rows current) /\
       ((0 : int) <= k /\ k < sac_columns current) /\
       ~(j = tid)) ==>
      sac_elts current j k = sac_elts previous j k`;

val sac_row_sorted_at_def = Define `
  sac_row_sorted_at
      (current : sac_matrix)
      (tid : int) <=>
    !j k : int.
      ((0 : int) <= j /\ j <= k /\ k < sac_columns current) ==>
      sac_elts current tid j <= sac_elts current tid k`;

val sac_row_permuted_at_def = Define `
  sac_row_permuted_at
      (current : sac_matrix)
      (previous : sac_matrix)
      (tid : int) <=>
    sac_map_permut
      (sac_elts current tid)
      (sac_elts previous tid)
      (0 : int)
      (sac_columns current)`;

val sac_transpose_finalization_vc_def = Define `
  sac_transpose_finalization_vc
      (current : sac_matrix)
      (original : sac_matrix) <=>
    sac_rows current = sac_columns current /\
    (!transposed : sac_matrix.
       sac_matrix_ok transposed ==>
       sac_dimensions transposed current ==>
       sac_transpose_relation current transposed ==>
       sac_final_columns transposed original)`;

val sac_row_step_vc_def = Define `
  sac_row_step_vc
      (original : sac_matrix)
      (current : sac_matrix)
      (n : int)
      (last : int) <=>
    !tid : int.
      (((0 : int) <= tid /\ tid <= last) /\
       sac_rows_permuted_from_columns current original n /\
       sac_rows_sorted_prefix current n tid) ==>
      (((0 : int) <= tid /\ tid < sac_rows current) /\
       (!next : sac_matrix.
          sac_matrix_ok next ==>
          sac_dimensions next current ==>
          (sac_unchanged_except_row next current tid /\
           sac_row_sorted_at next tid /\
           sac_row_permuted_at next current tid) ==>
          (sac_rows_permuted_from_columns next original n /\
           sac_rows_sorted_prefix
             next n (tid + (1 : int)))))`;

val sac_row_run_vc_def = Define `
  sac_row_run_vc
      (original : sac_matrix)
      (current : sac_matrix)
      (n : int)
      (last : int) <=>
    sac_row_step_vc original current n last /\
    ((sac_rows_permuted_from_columns current original n /\
      sac_rows_sorted_prefix current n (last + (1 : int))) ==>
     sac_transpose_finalization_vc current original)`;

val sac_transpose_branch_vc_def = Define `
  sac_transpose_branch_vc (original : sac_matrix) <=>
    let n = sac_rows original in
      sac_rows original = sac_columns original /\
      (!transposed : sac_matrix.
         sac_matrix_ok transposed ==>
         sac_dimensions transposed original ==>
         sac_transpose_relation original transposed ==>
         let last = sac_columns transposed - (1 : int) in
           (((0 : int) <= last + (1 : int) ==>
             ((sac_rows_permuted_from_columns
                 transposed original n /\
               sac_rows_sorted_prefix
                 transposed n (0 : int)) /\
              (!current : sac_matrix.
                 sac_matrix_ok current ==>
                 sac_dimensions current transposed ==>
                 sac_row_run_vc original current n last))) /\
            (last + (1 : int) < (0 : int) ==>
             sac_transpose_finalization_vc
               transposed original)))`;

val sac_sort_all_columns_vc_def = Define `
  sac_sort_all_columns_vc (original : sac_matrix) <=>
    (?result : bool.
       result = T \/
       sac_rows original = sac_columns original) /\
    (!choice : bool.
       (choice = T \/
        sac_rows original = sac_columns original) ==>
       if choice = T then
         sac_direct_branch_vc original
       else
         sac_transpose_branch_vc original)`;

val verifythis_2021_shearsort_ShearSort_sort_all_columnsqtvc_statement =
  ``!original : sac_matrix.
      sac_matrix_ok original ==>
      sac_sort_all_columns_vc original``;
