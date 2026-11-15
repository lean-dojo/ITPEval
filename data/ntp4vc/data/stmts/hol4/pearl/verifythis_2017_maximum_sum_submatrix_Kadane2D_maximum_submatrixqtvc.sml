(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_maximum_sum_submatrix_Kadane2D_maximum_submatrixqtvc:
  the generated verification condition for Kadane's two-dimensional
  maximum-sum submatrix algorithm over total integer-indexed arrays, including
  its row, column-update, and maximum-subarray loop invariants. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  maximum_submatrix_matrix =
    MaximumSubmatrixMatrix num num (int -> int -> int)
End

Datatype:
  maximum_submatrix_array =
    MaximumSubmatrixArray num (int -> int)
End

val maximum_submatrix_rows_def = Define `
  maximum_submatrix_rows
      (MaximumSubmatrixMatrix row_count column_count entries) =
    (&row_count : int)`;

val maximum_submatrix_columns_def = Define `
  maximum_submatrix_columns
      (MaximumSubmatrixMatrix row_count column_count entries) =
    (&column_count : int)`;

val maximum_submatrix_elts_def = Define `
  maximum_submatrix_elts
      (MaximumSubmatrixMatrix row_count column_count entries) =
    entries`;

val maximum_submatrix_array_length_def = Define `
  maximum_submatrix_array_length
      (MaximumSubmatrixArray array_length elements) =
    (&array_length : int)`;

val maximum_submatrix_get_def = Define `
  maximum_submatrix_get
      (MaximumSubmatrixArray array_length elements) (index : int) =
    elements index`;

val maximum_submatrix_array_update_def = Define `
  maximum_submatrix_array_update
      (MaximumSubmatrixArray array_length elements)
      (index : int) (value : int) =
    MaximumSubmatrixArray
      array_length
      (\q. if q = index then value else elements q)`;

val maximum_submatrix_update_fun_def = Define `
  maximum_submatrix_update_fun
      (f : int -> int) (index : int) (value : int) =
    \q. if q = index then value else f q`;

val maximum_submatrix_sum_count_def = Define `
  (maximum_submatrix_sum_count
      (f : int -> int) (start : int) 0 = (0 : int)) /\
  (maximum_submatrix_sum_count f start (SUC count) =
     f start +
       maximum_submatrix_sum_count
         f (start + (1 : int)) count)`;

val maximum_submatrix_sum_def = Define `
  maximum_submatrix_sum
      (f : int -> int) (lower : int) (upper : int) =
    if upper <= lower then
      (0 : int)
    else
      maximum_submatrix_sum_count
        f lower (Num (upper - lower))`;

val maximum_submatrix_array_sum_def = Define `
  maximum_submatrix_array_sum
      (a : maximum_submatrix_array) (lower : int) (upper : int) =
    maximum_submatrix_sum
      (maximum_submatrix_get a) lower upper`;

val maximum_submatrix_col_def = Define `
  maximum_submatrix_col
      (m : maximum_submatrix_matrix) (column : int) (row : int) =
    maximum_submatrix_elts m row column`;

val maximum_submatrix_matrix_sum_def = Define `
  maximum_submatrix_matrix_sum
      (m : maximum_submatrix_matrix)
      (row_lower : int) (row_upper : int)
      (column_lower : int) (column_upper : int) =
    maximum_submatrix_sum
      (\column.
         maximum_submatrix_sum
           (maximum_submatrix_col m column)
           row_lower row_upper)
      column_lower column_upper`;

val maximum_submatrix_valid_index_def = Define `
  maximum_submatrix_valid_index
      (m : maximum_submatrix_matrix) (row : int) (column : int) <=>
    ((0 : int) <= row /\ row < maximum_submatrix_rows m) /\
    (0 : int) <= column /\
    column < maximum_submatrix_columns m`;

val maximum_submatrix_legal_state_def = Define `
  maximum_submatrix_legal_state
      (m : maximum_submatrix_matrix)
      (row_lower : int) (row_upper : int)
      (column_lower : int) (column_upper : int)
      (maximum_sum : int) <=>
    ((0 : int) <= row_lower /\
     row_lower <= row_upper /\
     row_upper <= maximum_submatrix_rows m) /\
    ((0 : int) <= column_lower /\
     column_lower <= column_upper /\
     column_upper <= maximum_submatrix_columns m) /\
    (maximum_sum =
       maximum_submatrix_matrix_sum
         m row_lower row_upper column_lower column_upper /\
     (0 : int) <=
       maximum_submatrix_matrix_sum
         m row_lower row_upper column_lower column_upper)`;

val maximum_submatrix_processed_rows_def = Define `
  maximum_submatrix_processed_rows
      (m : maximum_submatrix_matrix)
      (row_limit : int) (maximum_sum : int) <=>
    !row_lower row_upper : int.
      (0 : int) <= row_lower /\ row_lower < row_limit ==>
      row_lower <= row_upper /\
      row_upper <= maximum_submatrix_rows m ==>
      !column_lower column_upper : int.
        (0 : int) <= column_lower /\
        column_lower <= column_upper /\
        column_upper <= maximum_submatrix_columns m ==>
        maximum_submatrix_matrix_sum
          m row_lower row_upper column_lower column_upper <=
        maximum_sum`;

val maximum_submatrix_lexicographic_bound_def = Define `
  maximum_submatrix_lexicographic_bound
      (m : maximum_submatrix_matrix)
      (current_row_lower : int) (row_upper_limit : int)
      (maximum_sum : int) <=>
    !row_lower row_upper : int.
      (0 : int) <= row_lower /\
      row_lower <= row_upper /\
      row_upper <= maximum_submatrix_rows m ==>
      row_lower < current_row_lower \/
      row_lower = current_row_lower /\
      row_upper < row_upper_limit ==>
      !column_lower column_upper : int.
        (0 : int) <= column_lower /\
        column_lower <= column_upper /\
        column_upper <= maximum_submatrix_columns m ==>
        maximum_submatrix_matrix_sum
          m row_lower row_upper column_lower column_upper <=
        maximum_sum`;

val maximum_submatrix_column_values_def = Define `
  maximum_submatrix_column_values
      (m : maximum_submatrix_matrix)
      (a : maximum_submatrix_array) (row_lower : int) (row_upper : int) <=>
    !column : int.
      (0 : int) <= column /\
      column < maximum_submatrix_columns m ==>
      maximum_submatrix_get a column =
        maximum_submatrix_sum
          (maximum_submatrix_col m column)
          row_lower row_upper`;

val maximum_submatrix_final_result_def = Define `
  maximum_submatrix_final_result
      (m : maximum_submatrix_matrix)
      (row_lower : int) (row_upper : int)
      (column_lower : int) (column_upper : int)
      (maximum_sum : int) <=>
    ((0 : int) <= row_lower /\
     row_lower <= row_upper /\
     row_upper <= maximum_submatrix_rows m) /\
    ((0 : int) <= column_lower /\
     column_lower <= column_upper /\
     column_upper <= maximum_submatrix_columns m) /\
    maximum_sum =
      maximum_submatrix_matrix_sum
        m row_lower row_upper column_lower column_upper /\
    !other_row_lower other_row_upper : int.
      (0 : int) <= other_row_lower /\
      other_row_lower <= other_row_upper /\
      other_row_upper <= maximum_submatrix_rows m ==>
      !other_column_lower other_column_upper : int.
        (0 : int) <= other_column_lower /\
        other_column_lower <= other_column_upper /\
        other_column_upper <= maximum_submatrix_columns m ==>
        maximum_submatrix_matrix_sum
          m other_row_lower other_row_upper
            other_column_lower other_column_upper <=
        maximum_sum`;

val maximum_submatrix_after_kadane_def = Define `
  maximum_submatrix_after_kadane
      (m : maximum_submatrix_matrix)
      (row_lower : int) (row_upper : int)
      (old_row_lower : int) (old_row_upper : int)
      (old_column_lower : int) (old_column_upper : int)
      (old_maximum_sum : int)
      (a : maximum_submatrix_array) (lo : int) (hi : int) <=>
    if old_maximum_sum <
         maximum_submatrix_array_sum a lo hi then
      maximum_submatrix_legal_state
        m row_lower row_upper lo hi
          (maximum_submatrix_array_sum a lo hi) /\
      maximum_submatrix_lexicographic_bound
        m row_lower (row_upper + (1 : int))
          (maximum_submatrix_array_sum a lo hi) /\
      maximum_submatrix_column_values
        m a row_lower (row_upper + (1 : int) - (1 : int))
    else
      maximum_submatrix_legal_state
        m old_row_lower old_row_upper
          old_column_lower old_column_upper old_maximum_sum /\
      maximum_submatrix_lexicographic_bound
        m row_lower (row_upper + (1 : int)) old_maximum_sum /\
      maximum_submatrix_column_values
        m a row_lower (row_upper + (1 : int) - (1 : int))`;

val maximum_submatrix_kadane_call_def = Define `
  maximum_submatrix_kadane_call
      (m : maximum_submatrix_matrix)
      (row_lower : int) (row_upper : int)
      (old_row_lower : int) (old_row_upper : int)
      (old_column_lower : int) (old_column_upper : int)
      (old_maximum_sum : int)
      (a : maximum_submatrix_array) <=>
    !lo hi : int.
      ((0 : int) <= lo /\
       lo <= hi /\
       hi <= maximum_submatrix_array_length a) /\
      (!lower upper : int.
         (0 : int) <= lower /\
         lower <= upper /\
         upper <= maximum_submatrix_array_length a ==>
         maximum_submatrix_array_sum a lower upper <=
           maximum_submatrix_array_sum a lo hi) ==>
      maximum_submatrix_after_kadane
        m row_lower row_upper
          old_row_lower old_row_upper
          old_column_lower old_column_upper old_maximum_sum
          a lo hi`;

val maximum_submatrix_column_loop_invariant_def = Define `
  maximum_submatrix_column_loop_invariant
      (m : maximum_submatrix_matrix)
      (a : maximum_submatrix_array)
      (row_lower : int) (row_upper : int)
      (last_column : int) (column : int) <=>
    ((0 : int) <= column /\ column <= last_column) /\
    (!j : int.
       (0 : int) <= j /\ j < column ==>
       maximum_submatrix_get a j =
         maximum_submatrix_sum
           (maximum_submatrix_col m j)
           row_lower row_upper) /\
    (!j : int.
       column <= j /\ j < maximum_submatrix_columns m ==>
       maximum_submatrix_get a j =
         maximum_submatrix_sum
           (maximum_submatrix_col m j)
           row_lower (row_upper - (1 : int)))`;

val maximum_submatrix_column_update_def = Define `
  maximum_submatrix_column_update
      (m : maximum_submatrix_matrix)
      (a : maximum_submatrix_array)
      (row_lower : int) (row_upper : int)
      (column : int) <=>
    let previous_row = row_upper - (1 : int)
    in
      maximum_submatrix_valid_index m previous_row column /\
      ((0 : int) <= column /\
       column < maximum_submatrix_array_length a) /\
      let new_value =
        maximum_submatrix_get a column +
          maximum_submatrix_elts m previous_row column
      in
        ((0 : int) <= column /\
         column < maximum_submatrix_array_length a) /\
        (maximum_submatrix_array_length
           (maximum_submatrix_array_update a column new_value) =
           maximum_submatrix_array_length a ==>
         maximum_submatrix_get
           (maximum_submatrix_array_update a column new_value) =
           maximum_submatrix_update_fun
             (maximum_submatrix_get a) column new_value ==>
         (!j : int.
            (0 : int) <= j /\ j < column + (1 : int) ==>
            maximum_submatrix_get
              (maximum_submatrix_array_update a column new_value) j =
              maximum_submatrix_sum
                (maximum_submatrix_col m j)
                row_lower row_upper) /\
         (!j : int.
            column + (1 : int) <= j /\
            j < maximum_submatrix_columns m ==>
            maximum_submatrix_get
              (maximum_submatrix_array_update a column new_value) j =
              maximum_submatrix_sum
                (maximum_submatrix_col m j)
                row_lower (row_upper - (1 : int))))`;

val maximum_submatrix_column_phase_def = Define `
  maximum_submatrix_column_phase
      (m : maximum_submatrix_matrix)
      (row_lower : int) (row_upper : int)
      (old_row_lower : int) (old_row_upper : int)
      (old_column_lower : int) (old_column_upper : int)
      (old_maximum_sum : int)
      (a : maximum_submatrix_array) <=>
    let last_column = maximum_submatrix_columns m - (1 : int)
    in
      (((0 : int) <= last_column + (1 : int) ==>
        ((!j : int.
            (0 : int) <= j /\ j < (0 : int) ==>
            maximum_submatrix_get a j =
              maximum_submatrix_sum
                (maximum_submatrix_col m j)
                row_lower row_upper) /\
         (!j : int.
            (0 : int) <= j /\
            j < maximum_submatrix_columns m ==>
            maximum_submatrix_get a j =
              maximum_submatrix_sum
                (maximum_submatrix_col m j)
                row_lower (row_upper - (1 : int)))) /\
        (!updated : maximum_submatrix_array.
           maximum_submatrix_array_length updated = maximum_submatrix_array_length a ==>
           ((!column : int.
               maximum_submatrix_column_loop_invariant
                 m updated row_lower row_upper
                   last_column column ==>
               maximum_submatrix_column_update
                 m updated row_lower row_upper column) /\
            (((!j : int.
                 (0 : int) <= j /\
                 j < last_column + (1 : int) ==>
                 maximum_submatrix_get updated j =
                   maximum_submatrix_sum
                     (maximum_submatrix_col m j)
                     row_lower row_upper) /\
              (!j : int.
                 last_column + (1 : int) <= j /\
                 j < maximum_submatrix_columns m ==>
                 maximum_submatrix_get updated j =
                   maximum_submatrix_sum
                     (maximum_submatrix_col m j)
                     row_lower (row_upper - (1 : int)))) ==>
             maximum_submatrix_kadane_call
               m row_lower row_upper
                 old_row_lower old_row_upper
                 old_column_lower old_column_upper old_maximum_sum
                 updated)))) /\
       (last_column + (1 : int) < (0 : int) ==>
        maximum_submatrix_kadane_call
          m row_lower row_upper
            old_row_lower old_row_upper
            old_column_lower old_column_upper old_maximum_sum
            a))`;

val maximum_submatrix_inner_invariant_def = Define `
  maximum_submatrix_inner_invariant
      (m : maximum_submatrix_matrix)
      (first_row_upper : int) (last_row : int)
      (row_lower : int) (row_upper : int)
      (best_row_lower : int) (best_row_upper : int)
      (best_column_lower : int) (best_column_upper : int)
      (best_sum : int) (a : maximum_submatrix_array) <=>
    (first_row_upper <= row_upper /\ row_upper <= last_row) /\
    maximum_submatrix_legal_state
      m best_row_lower best_row_upper
        best_column_lower best_column_upper best_sum /\
    maximum_submatrix_lexicographic_bound
      m row_lower row_upper best_sum /\
    maximum_submatrix_column_values
      m a row_lower (row_upper - (1 : int))`;

val maximum_submatrix_inner_finish_def = Define `
  maximum_submatrix_inner_finish
      (m : maximum_submatrix_matrix)
      (row_lower : int) (last_row : int)
      (best_row_lower : int) (best_row_upper : int)
      (best_column_lower : int) (best_column_upper : int)
      (best_sum : int) (a : maximum_submatrix_array) <=>
    (maximum_submatrix_legal_state
       m best_row_lower best_row_upper
         best_column_lower best_column_upper best_sum /\
     maximum_submatrix_lexicographic_bound
       m row_lower (last_row + (1 : int)) best_sum /\
     maximum_submatrix_column_values
       m a row_lower (last_row + (1 : int) - (1 : int))) ==>
    maximum_submatrix_legal_state
      m best_row_lower best_row_upper
        best_column_lower best_column_upper best_sum /\
    maximum_submatrix_processed_rows
      m (row_lower + (1 : int)) best_sum`;

val maximum_submatrix_after_fill_def = Define `
  maximum_submatrix_after_fill
      (m : maximum_submatrix_matrix)
      (row_lower : int)
      (best_row_lower : int) (best_row_upper : int)
      (best_column_lower : int) (best_column_upper : int)
      (best_sum : int) (a : maximum_submatrix_array) <=>
    let last_row = maximum_submatrix_rows m
    in
    let first_row_upper = row_lower + (1 : int)
    in
      ((first_row_upper <= last_row + (1 : int) ==>
        maximum_submatrix_legal_state
          m best_row_lower best_row_upper
            best_column_lower best_column_upper best_sum /\
        maximum_submatrix_lexicographic_bound
          m row_lower first_row_upper best_sum /\
        maximum_submatrix_column_values
          m a row_lower (first_row_upper - (1 : int)) /\
        !next_row_lower next_row_upper : int.
        !next_column_lower next_column_upper : int.
        !next_best_sum : int.
        !next_a : maximum_submatrix_array.
          maximum_submatrix_array_length next_a = maximum_submatrix_array_length a ==>
          ((!row_upper : int.
              maximum_submatrix_inner_invariant
                m first_row_upper last_row row_lower row_upper
                  next_row_lower next_row_upper
                  next_column_lower next_column_upper
                  next_best_sum next_a ==>
              maximum_submatrix_column_phase
                m row_lower row_upper
                  next_row_lower next_row_upper
                  next_column_lower next_column_upper
                  next_best_sum next_a) /\
           maximum_submatrix_inner_finish
              m row_lower last_row
                next_row_lower next_row_upper
                next_column_lower next_column_upper
                next_best_sum next_a)) /\
       (last_row + (1 : int) < first_row_upper ==>
        maximum_submatrix_legal_state
          m best_row_lower best_row_upper
            best_column_lower best_column_upper best_sum /\
        maximum_submatrix_processed_rows
          m (row_lower + (1 : int)) best_sum))`;

val maximum_submatrix_fill_phase_def = Define `
  maximum_submatrix_fill_phase
      (m : maximum_submatrix_matrix)
      (row_lower : int)
      (best_row_lower : int) (best_row_upper : int)
      (best_column_lower : int) (best_column_upper : int)
      (best_sum : int) (a : maximum_submatrix_array) <=>
    let column_count = maximum_submatrix_columns m
    in
      ((0 : int) <= (0 : int) /\
       (0 : int) <= column_count /\
       (0 : int) + column_count <= maximum_submatrix_array_length a) /\
      !filled : maximum_submatrix_array.
        maximum_submatrix_array_length filled = maximum_submatrix_array_length a ==>
        (((!i : int.
             ((0 : int) <= i /\ i < (0 : int)) \/
             ((0 : int) + column_count <= i /\
              i < maximum_submatrix_array_length filled) ==>
             maximum_submatrix_get filled i =
               maximum_submatrix_get a i) /\
          (!i : int.
             (0 : int) <= i /\
             i < (0 : int) + column_count ==>
             maximum_submatrix_get filled i = (0 : int))) ==>
         maximum_submatrix_after_fill
           m row_lower
             best_row_lower best_row_upper
             best_column_lower best_column_upper best_sum
             filled)`;

val maximum_submatrix_outer_invariant_def = Define `
  maximum_submatrix_outer_invariant
      (m : maximum_submatrix_matrix)
      (last_row_lower : int) (row_lower : int)
      (best_row_lower : int) (best_row_upper : int)
      (best_column_lower : int) (best_column_upper : int)
      (best_sum : int) <=>
    ((0 : int) <= row_lower /\ row_lower <= last_row_lower) /\
    maximum_submatrix_legal_state
      m best_row_lower best_row_upper
        best_column_lower best_column_upper best_sum /\
    maximum_submatrix_processed_rows m row_lower best_sum`;

val maximum_submatrix_outer_body_def = Define `
  maximum_submatrix_outer_body
      (m : maximum_submatrix_matrix)
      (initial_array : maximum_submatrix_array) (last_row_lower : int) <=>
    !best_row_lower best_row_upper : int.
    !best_column_lower best_column_upper : int.
    !best_sum : int.
    !a : maximum_submatrix_array.
      maximum_submatrix_array_length a = maximum_submatrix_array_length initial_array ==>
      !row_lower : int.
        maximum_submatrix_outer_invariant
          m last_row_lower row_lower
            best_row_lower best_row_upper
            best_column_lower best_column_upper best_sum ==>
        maximum_submatrix_fill_phase
          m row_lower
            best_row_lower best_row_upper
            best_column_lower best_column_upper best_sum
            a`;

val maximum_submatrix_Kadane2D_maximum_submatrixqtvc_statement =
  ``!m : maximum_submatrix_matrix.
      let column_count = maximum_submatrix_columns m
      in
        (0 : int) <= column_count /\
        !initial_array : maximum_submatrix_array.
          ((!i : int.
              (0 : int) <= i /\ i < column_count ==>
              maximum_submatrix_get initial_array i = (0 : int)) /\
           maximum_submatrix_array_length initial_array = column_count) ==>
          let last_row_lower =
            maximum_submatrix_rows m - (1 : int)
          in
            (((0 : int) <= last_row_lower + (1 : int) ==>
              maximum_submatrix_legal_state
                m (0 : int) (0 : int)
                  (0 : int) (0 : int) (0 : int) /\
              maximum_submatrix_processed_rows
                m (0 : int) (0 : int) /\
              maximum_submatrix_outer_body
                m initial_array last_row_lower) /\
             (!best_row_lower best_row_upper : int.
              !best_column_lower best_column_upper : int.
              !best_sum : int.
                (maximum_submatrix_legal_state
                   m best_row_lower best_row_upper
                     best_column_lower best_column_upper best_sum /\
                 maximum_submatrix_processed_rows
                   m (last_row_lower + (1 : int)) best_sum) ==>
                maximum_submatrix_final_result
                  m best_row_lower best_row_upper
                    best_column_lower best_column_upper best_sum)) /\
            (last_row_lower + (1 : int) < (0 : int) ==>
             maximum_submatrix_final_result
               m (0 : int) (0 : int)
                 (0 : int) (0 : int) (0 : int))``;
