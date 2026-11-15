(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_modified_Top_shearsortqtvc: the
  verification condition for alternating snake-ordered row sorts and
  sorted column passes while preserving matrix multiplicities and
  decreasing the inversion count. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory pairTheory;

val _ = type_abbrev
  ("sm_matrix", ``:int # (int # (int -> int -> int))``);

val sm_to_num_def = Define `
  sm_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sm_rows_def = Define `
  sm_rows (m : sm_matrix) = FST m`;

val sm_columns_def = Define `
  sm_columns (m : sm_matrix) = FST (SND m)`;

val sm_elts_def = Define `
  sm_elts (m : sm_matrix) = SND (SND m)`;

val sm_matrix_ok_def = Define `
  sm_matrix_ok (m : sm_matrix) <=>
    (0 : int) <= sm_rows m /\ (0 : int) <= sm_columns m`;

val sm_same_dimensions_def = Define `
  sm_same_dimensions (left : sm_matrix) (right : sm_matrix) <=>
    sm_rows left = sm_rows right /\
    sm_columns left = sm_columns right`;

val sm_sum_def = Define `
  sm_sum (f : int -> int) (lower : int) (upper : int) =
    FOLDL
      (\acc value : int. acc + value)
      (0 : int)
      (GENLIST
        (\offset : num. f (lower + &offset))
        (sm_to_num (upper - lower)))`;

val sm_tmod_def = Define `
  sm_tmod (numerator : int) (denominator : int) =
    numerator rem denominator`;

val sm_snake_lt_def = Define `
  sm_snake_lt (i : int) (j : int) (k : int) (l : int) <=>
    i < k \/
    (i = k /\
     if sm_tmod i (2 : int) = (0 : int) then j < l else l < j)`;

val sm_mocc_def = Define `
  sm_mocc (value : int) (m : sm_matrix) =
    sm_sum
      (\row : int.
        sm_sum
          (\column : int.
            if sm_elts m row column = value then (1 : int) else (0 : int))
          (0 : int)
          (sm_columns m))
      (0 : int)
      (sm_rows m)`;

val sm_inversions_def = Define `
  sm_inversions (m : sm_matrix) =
    sm_sum
      (\i : int.
        sm_sum
          (\j : int.
            sm_sum
              (\k : int.
                sm_sum
                  (\l : int.
                    if sm_snake_lt i j k l /\
                       sm_elts m k l < sm_elts m i j
                    then (1 : int)
                    else (0 : int))
                  (0 : int)
                  (sm_columns m))
              (0 : int)
              (sm_rows m))
          (0 : int)
          (sm_columns m))
      (0 : int)
      (sm_rows m)`;

val sm_mocc_preserved_def = Define `
  sm_mocc_preserved (current : sm_matrix) (original : sm_matrix) <=>
    !value : int.
      sm_mocc value current = sm_mocc value original`;

val sm_sorted_row_def = Define `
  sm_sorted_row
      (m : sm_matrix)
      (row : int)
      (ascending : bool) <=>
    ((0 : int) <= row /\ row < sm_rows m) /\
    if ascending then
      !j l : int.
        (0 : int) <= j /\ j <= l /\ l < sm_columns m ==>
        sm_elts m row j <= sm_elts m row l
    else
      !j l : int.
        (0 : int) <= j /\ j <= l /\ l < sm_columns m ==>
        sm_elts m row l <= sm_elts m row j`;

val sm_sorted_column_def = Define `
  sm_sorted_column (m : sm_matrix) (column : int) <=>
    ((0 : int) <= column /\ column < sm_columns m) /\
    !i k : int.
      (0 : int) <= i /\ i <= k /\ k < sm_rows m ==>
      sm_elts m i column <= sm_elts m k column`;

val sm_rows_sorted_before_def = Define `
  sm_rows_sorted_before (m : sm_matrix) (upper : int) <=>
    !row : int.
      (0 : int) <= row /\ row < upper ==>
      sm_sorted_row
        m row (sm_tmod row (2 : int) = (0 : int))`;

val sm_columns_sorted_before_def = Define `
  sm_columns_sorted_before (m : sm_matrix) (upper : int) <=>
    !column : int.
      (0 : int) <= column /\ column < upper ==>
      sm_sorted_column m column`;

val sm_snake_order_def = Define `
  sm_snake_order (m : sm_matrix) <=>
    !i j k l : int.
      (0 : int) <= i /\ i < sm_rows m ==>
      (0 : int) <= j /\ j < sm_columns m ==>
      (0 : int) <= k /\ k < sm_rows m ==>
      (0 : int) <= l /\ l < sm_columns m ==>
      sm_snake_lt i j k l ==>
      sm_elts m i j <= sm_elts m k l`;

val sm_square_order_def = Define `
  sm_square_order (m : sm_matrix) (bound : int) <=>
    !i j k l : int.
      (((0 : int) <= i /\ i < bound) /\
       ((0 : int) <= j /\ j < bound) /\
       ((0 : int) <= k /\ k < bound) /\
       ((0 : int) <= l /\ l < bound) /\
       sm_snake_lt i j k l) ==>
      sm_elts m i j <= sm_elts m k l`;

val sm_row_frame_def = Define `
  sm_row_frame
      (after : sm_matrix)
      (before : sm_matrix)
      (selected_row : int) <=>
    !row column : int.
      (0 : int) <= row /\ row < sm_rows after ==>
      (0 : int) <= column /\ column < sm_columns after ==>
      ~(row = selected_row) ==>
      sm_elts after row column = sm_elts before row column`;

val sm_column_frame_def = Define `
  sm_column_frame
      (after : sm_matrix)
      (before : sm_matrix)
      (selected_column : int) <=>
    !row column : int.
      (0 : int) <= row /\ row < sm_rows after ==>
      (0 : int) <= column /\ column < sm_columns after ==>
      ~(column = selected_column) ==>
      sm_elts after row column = sm_elts before row column`;

val sm_matrices_equal_on_range_def = Define `
  sm_matrices_equal_on_range
      (left : sm_matrix)
      (right : sm_matrix) <=>
    !row column : int.
      (0 : int) <= row /\ row < sm_rows left ==>
      (0 : int) <= column /\ column < sm_columns left ==>
      sm_elts left row column = sm_elts right row column`;

val sm_selected_column_unchanged_def = Define `
  sm_selected_column_unchanged
      (after : sm_matrix)
      (before : sm_matrix)
      (selected_column : int) <=>
    !row : int.
      (0 : int) <= row /\ row < sm_rows after ==>
      sm_elts after row selected_column =
      sm_elts before row selected_column`;

val sm_column_sort_post_def = Define `
  sm_column_sort_post
      (after : sm_matrix)
      (before : sm_matrix)
      (selected_column : int)
      (nochange : bool) <=>
    sm_column_frame after before selected_column /\
    sm_mocc_preserved after before /\
    (nochange ==>
      sm_selected_column_unchanged after before selected_column) /\
    sm_sorted_column after selected_column /\
    sm_inversions after <= sm_inversions before /\
    (~nochange ==> sm_inversions after < sm_inversions before)`;

val sm_column_updated_state_def = Define `
  sm_column_updated_state
      (original : sm_matrix)
      (phase_start : sm_matrix)
      (new_nochange : bool)
      (after : sm_matrix)
      (next_column : int) <=>
    (new_nochange ==>
      sm_matrices_equal_on_range after phase_start) /\
    sm_columns_sorted_before after next_column /\
    sm_mocc_preserved after original /\
    sm_inversions after <= sm_inversions phase_start /\
    (~new_nochange ==>
      sm_inversions after < sm_inversions phase_start)`;

val sm_all_column_return_flags_def = Define `
  sm_all_column_return_flags
      (original : sm_matrix)
      (phase_start : sm_matrix)
      (old_nochange : bool)
      (before : sm_matrix)
      (after : sm_matrix)
      (selected_column : int) <=>
    !returned_nochange : bool.
      sm_column_sort_post
        after before selected_column returned_nochange ==>
      sm_column_updated_state
        original
        phase_start
        (if ~returned_nochange then F else old_nochange)
        after
        (selected_column + (1 : int))`;

val sm_all_column_sort_results_def = Define `
  sm_all_column_sort_results
      (original : sm_matrix)
      (phase_start : sm_matrix)
      (old_nochange : bool)
      (before : sm_matrix)
      (selected_column : int) <=>
    !after : sm_matrix.
      sm_matrix_ok after ==>
      sm_same_dimensions after before ==>
      sm_all_column_return_flags
        original
        phase_start
        old_nochange
        before
        after
        selected_column`;

val sm_column_loop_state_def = Define `
  sm_column_loop_state
      (original : sm_matrix)
      (phase_start : sm_matrix)
      (nochange : bool)
      (current : sm_matrix)
      (column : int)
      (last_column : int) <=>
    ((0 : int) <= column /\ column <= last_column) /\
    (nochange ==>
      sm_matrices_equal_on_range current phase_start) /\
    sm_columns_sorted_before current column /\
    sm_mocc_preserved current original /\
    sm_inversions current <= sm_inversions phase_start /\
    (~nochange ==>
      sm_inversions current < sm_inversions phase_start)`;

val sm_column_index_obligation_def = Define `
  sm_column_index_obligation
      (original : sm_matrix)
      (phase_start : sm_matrix)
      (nochange : bool)
      (current : sm_matrix)
      (column : int) <=>
    ((0 : int) <= column /\ column < sm_columns current) /\
    sm_all_column_sort_results
      original phase_start nochange current column`;

val sm_all_column_indices_def = Define `
  sm_all_column_indices
      (original : sm_matrix)
      (phase_start : sm_matrix)
      (nochange : bool)
      (current : sm_matrix)
      (last_column : int) <=>
    !column : int.
      sm_column_loop_state
        original phase_start nochange current column last_column ==>
      sm_column_index_obligation
        original phase_start nochange current column`;

val sm_column_loop_exit_state_def = Define `
  sm_column_loop_exit_state
      (original : sm_matrix)
      (phase_start : sm_matrix)
      (nochange : bool)
      (current : sm_matrix)
      (upper : int) <=>
    (nochange ==>
      sm_matrices_equal_on_range current phase_start) /\
    sm_columns_sorted_before current upper /\
    sm_mocc_preserved current original /\
    sm_inversions current <= sm_inversions phase_start /\
    (~nochange ==>
      sm_inversions current < sm_inversions phase_start)`;

val sm_column_loop_exit_result_def = Define `
  sm_column_loop_exit_result
      (original : sm_matrix)
      (outer_baseline : sm_matrix)
      (nochange : bool)
      (current : sm_matrix) <=>
    if nochange then
      sm_square_order current (sm_columns original) /\
      sm_snake_order current /\
      sm_mocc_preserved current original
    else
      ((0 : int) <= sm_inversions outer_baseline /\
       sm_inversions current < sm_inversions outer_baseline) /\
      sm_mocc_preserved current original`;

val sm_all_column_loop_states_def = Define `
  sm_all_column_loop_states
      (original : sm_matrix)
      (outer_baseline : sm_matrix)
      (phase_start : sm_matrix)
      (last_column : int) <=>
    !nochange : bool.
    !current : sm_matrix.
      sm_matrix_ok current ==>
      sm_same_dimensions current phase_start ==>
      (sm_all_column_indices
         original phase_start nochange current last_column /\
       (sm_column_loop_exit_state
          original
          phase_start
          nochange
          current
          (last_column + (1 : int)) ==>
        sm_column_loop_exit_result
          original outer_baseline nochange current))`;

val sm_column_phase_def = Define `
  sm_column_phase
      (original : sm_matrix)
      (outer_baseline : sm_matrix)
      (phase_start : sm_matrix) <=>
    let last_column = sm_columns original - (1 : int)
    in
      (((0 : int) <= last_column + (1 : int) ==>
        (sm_columns_sorted_before phase_start (0 : int) /\
         sm_mocc_preserved phase_start original /\
         sm_inversions phase_start <= sm_inversions phase_start) /\
        sm_all_column_loop_states
          original outer_baseline phase_start last_column) /\
       (last_column + (1 : int) < (0 : int) ==>
        sm_square_order phase_start (sm_columns original) /\
        sm_snake_order phase_start /\
        sm_mocc_preserved phase_start original))`;

val sm_row_sort_post_def = Define `
  sm_row_sort_post
      (after : sm_matrix)
      (before : sm_matrix)
      (selected_row : int) <=>
    sm_row_frame after before selected_row /\
    sm_mocc_preserved after before /\
    sm_sorted_row
      after
      selected_row
      (sm_tmod selected_row (2 : int) = (0 : int)) /\
    sm_inversions after <= sm_inversions before`;

val sm_row_updated_state_def = Define `
  sm_row_updated_state
      (original : sm_matrix)
      (row_baseline : sm_matrix)
      (after : sm_matrix)
      (next_row : int) <=>
    sm_rows_sorted_before after next_row /\
    sm_mocc_preserved after original /\
    sm_inversions after <= sm_inversions row_baseline`;

val sm_all_row_sort_results_def = Define `
  sm_all_row_sort_results
      (original : sm_matrix)
      (row_baseline : sm_matrix)
      (before : sm_matrix)
      (selected_row : int) <=>
    !after : sm_matrix.
      sm_matrix_ok after ==>
      sm_same_dimensions after before ==>
      sm_row_sort_post after before selected_row ==>
      sm_row_updated_state
        original
        row_baseline
        after
        (selected_row + (1 : int))`;

val sm_row_loop_state_def = Define `
  sm_row_loop_state
      (original : sm_matrix)
      (row_baseline : sm_matrix)
      (current : sm_matrix)
      (row : int)
      (last_row : int) <=>
    ((0 : int) <= row /\ row <= last_row) /\
    sm_rows_sorted_before current row /\
    sm_mocc_preserved current original /\
    sm_inversions current <= sm_inversions row_baseline`;

val sm_row_index_obligation_def = Define `
  sm_row_index_obligation
      (original : sm_matrix)
      (row_baseline : sm_matrix)
      (current : sm_matrix)
      (row : int) <=>
    ~((2 : int) = (0 : int)) /\
    ((0 : int) <= row /\ row < sm_rows current) /\
    sm_all_row_sort_results
      original row_baseline current row`;

val sm_all_row_indices_def = Define `
  sm_all_row_indices
      (original : sm_matrix)
      (row_baseline : sm_matrix)
      (current : sm_matrix)
      (last_row : int) <=>
    !row : int.
      sm_row_loop_state
        original row_baseline current row last_row ==>
      sm_row_index_obligation
        original row_baseline current row`;

val sm_row_loop_exit_state_def = Define `
  sm_row_loop_exit_state
      (original : sm_matrix)
      (row_baseline : sm_matrix)
      (current : sm_matrix)
      (upper : int) <=>
    sm_rows_sorted_before current upper /\
    sm_mocc_preserved current original /\
    sm_inversions current <= sm_inversions row_baseline`;

val sm_all_row_loop_states_def = Define `
  sm_all_row_loop_states
      (original : sm_matrix)
      (row_baseline : sm_matrix)
      (last_row : int) <=>
    !current : sm_matrix.
      sm_matrix_ok current ==>
      sm_same_dimensions current row_baseline ==>
      (sm_all_row_indices
         original row_baseline current last_row /\
       (sm_row_loop_exit_state
          original
          row_baseline
          current
          (last_row + (1 : int)) ==>
        sm_column_phase original row_baseline current))`;

val sm_shearsort_vc_def = Define `
  sm_shearsort_vc
      (original : sm_matrix)
      (row_baseline : sm_matrix) <=>
    let last_row = sm_columns original - (1 : int)
    in
      (((0 : int) <= last_row + (1 : int) ==>
        (sm_rows_sorted_before row_baseline (0 : int) /\
         sm_mocc_preserved row_baseline original /\
         sm_inversions row_baseline <= sm_inversions row_baseline) /\
        sm_all_row_loop_states original row_baseline last_row) /\
       (last_row + (1 : int) < (0 : int) ==>
        sm_column_phase original row_baseline row_baseline))`;

val verifythis_2021_shearsort_modified_Top_shearsortqtvc_statement =
  ``!original row_baseline : sm_matrix.
      sm_matrix_ok original ==>
      sm_matrix_ok row_baseline ==>
      sm_rows original = sm_columns original ==>
      sm_rows row_baseline = sm_rows original ==>
      sm_columns row_baseline = sm_columns original ==>
      sm_mocc_preserved row_baseline original ==>
      sm_shearsort_vc original row_baseline``;
