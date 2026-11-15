(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc: the
  verification condition for sorting every row of an integer matrix in
  alternating ascending and descending order while preserving each row's
  multiset. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val _ = type_abbrev
  ("sar_matrix", ``:int # (int # (int -> int -> int))``);

val sar_to_num_def = Define `
  sar_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sar_rows_def = Define `
  sar_rows (m : sar_matrix) = FST m`;

val sar_columns_def = Define `
  sar_columns (m : sar_matrix) = FST (SND m)`;

val sar_elts_def = Define `
  sar_elts (m : sar_matrix) = SND (SND m)`;

val sar_matrix_ok_def = Define `
  sar_matrix_ok (m : sar_matrix) <=>
    (0 : int) <= sar_rows m /\ (0 : int) <= sar_columns m`;

val sar_dimensions_def = Define `
  sar_dimensions (current : sar_matrix) (previous : sar_matrix) <=>
    sar_rows current = sar_rows previous /\
    sar_columns current = sar_columns previous`;

val sar_occurrences_def = Define `
  sar_occurrences
      (value : int)
      (f : int -> int)
      (lower : int)
      (upper : int) =
    &(LENGTH
        (FILTER
          (\index : int. f index = value)
          (GENLIST
            (\offset : num. lower + &offset)
            (sar_to_num (upper - lower)))))`;

val sar_map_permut_def = Define `
  sar_map_permut
      (first_map : int -> int)
      (second_map : int -> int)
      (lower : int)
      (upper : int) <=>
    !value : int.
      sar_occurrences value first_map lower upper =
      sar_occurrences value second_map lower upper`;

val sar_rows_permuted_def = Define `
  sar_rows_permuted
      (current : sar_matrix)
      (original : sar_matrix) <=>
    !i : int.
      ((0 : int) <= i /\ i < sar_rows current) ==>
      sar_map_permut
        (sar_elts current i)
        (sar_elts original i)
        (0 : int)
        (sar_columns current)`;

val sar_rows_sorted_prefix_def = Define `
  sar_rows_sorted_prefix
      (current : sar_matrix)
      (limit : int) <=>
    !i j k : int.
      (((0 : int) <= i /\ i < limit) /\
       (0 : int) <= j /\ j <= k /\ k < sar_columns current) ==>
      if i % (2 : int) = (0 : int) then
        sar_elts current i j <= sar_elts current i k
      else
        sar_elts current i k <= sar_elts current i j`;

val sar_final_rows_def = Define `
  sar_final_rows
      (current : sar_matrix)
      (original : sar_matrix) <=>
    sar_rows_permuted current original /\
    sar_rows_sorted_prefix current (sar_rows current)`;

val sar_unchanged_except_row_def = Define `
  sar_unchanged_except_row
      (current : sar_matrix)
      (previous : sar_matrix)
      (tid : int) <=>
    !j k : int.
      ((0 : int) <= j /\ j < sar_rows current /\
       ((0 : int) <= k /\ k < sar_columns current) /\
       ~(j = tid)) ==>
      sar_elts current j k = sar_elts previous j k`;

val sar_row_sorted_at_def = Define `
  sar_row_sorted_at
      (current : sar_matrix)
      (tid : int) <=>
    !j k : int.
      ((0 : int) <= j /\ j <= k /\ k < sar_columns current) ==>
      if tid % (2 : int) = (0 : int) then
        sar_elts current tid j <= sar_elts current tid k
      else
        sar_elts current tid k <= sar_elts current tid j`;

val sar_row_permuted_at_def = Define `
  sar_row_permuted_at
      (current : sar_matrix)
      (previous : sar_matrix)
      (tid : int) <=>
    sar_map_permut
      (sar_elts current tid)
      (sar_elts previous tid)
      (0 : int)
      (sar_columns current)`;

val sar_step_vc_def = Define `
  sar_step_vc
      (original : sar_matrix)
      (current : sar_matrix)
      (last : int) <=>
    !tid : int.
      (((0 : int) <= tid /\ tid <= last) /\
       sar_rows_permuted current original /\
       sar_rows_sorted_prefix current tid) ==>
      (~((2 : int) = (0 : int)) /\
       ((0 : int) <= tid /\ tid < sar_rows current) /\
       (!next : sar_matrix.
          sar_matrix_ok next ==>
          sar_dimensions next current ==>
          (sar_unchanged_except_row next current tid /\
           sar_row_sorted_at next tid /\
           sar_row_permuted_at next current tid) ==>
          (sar_rows_permuted next original /\
           sar_rows_sorted_prefix next (tid + (1 : int)))))`;

val sar_run_vc_def = Define `
  sar_run_vc
      (original : sar_matrix)
      (current : sar_matrix)
      (last : int) <=>
    sar_step_vc original current last /\
    ((sar_rows_permuted current original /\
      sar_rows_sorted_prefix current (last + (1 : int))) ==>
     sar_final_rows current original)`;

val sar_sort_all_rows_vc_def = Define `
  sar_sort_all_rows_vc (original : sar_matrix) <=>
    let last = sar_rows original - (1 : int) in
      (((0 : int) <= last + (1 : int) ==>
        ((sar_rows_permuted original original /\
          sar_rows_sorted_prefix original (0 : int)) /\
         (!current : sar_matrix.
            sar_matrix_ok current ==>
            sar_dimensions current original ==>
            sar_run_vc original current last))) /\
       (last + (1 : int) < (0 : int) ==>
        sar_final_rows original original))`;

val verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc_statement =
  ``!original : sar_matrix.
      sar_matrix_ok original ==>
      sar_sort_all_rows_vc original``;
