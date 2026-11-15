(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_columnqtvc: the verification
  condition for copying an integer-matrix column into a list, sorting it,
  and writing it back while preserving the other columns and the column's
  multiset. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val _ = type_abbrev
  ("sc_matrix", ``:int # (int # (int -> int -> int))``);

val sc_to_num_def = Define `
  sc_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sc_rows_def = Define `
  sc_rows (m : sc_matrix) = FST m`;

val sc_columns_def = Define `
  sc_columns (m : sc_matrix) = FST (SND m)`;

val sc_elts_def = Define `
  sc_elts (m : sc_matrix) = SND (SND m)`;

val sc_matrix_ok_def = Define `
  sc_matrix_ok (m : sc_matrix) <=>
    (0 : int) <= sc_rows m /\ (0 : int) <= sc_columns m`;

val sc_dimensions_def = Define `
  sc_dimensions (current : sc_matrix) (previous : sc_matrix) <=>
    sc_rows current = sc_rows previous /\
    sc_columns current = sc_columns previous`;

val sc_valid_index_def = Define `
  sc_valid_index (m : sc_matrix) (i : int) (j : int) <=>
    ((0 : int) <= i /\ i < sc_rows m) /\
    (0 : int) <= j /\ j < sc_columns m`;

val sc_get_def = Define `
  sc_get (xs : int list) (i : int) =
    if sc_to_num i < LENGTH xs then EL (sc_to_num i) xs else (0 : int)`;

val sc_fun_update_def = Define `
  sc_fun_update (f : 'a -> 'b) (key : 'a) (value : 'b) =
    \query. if query = key then value else f query`;

val sc_occurrences_def = Define `
  sc_occurrences
      (value : int)
      (f : int -> int)
      (lower : int)
      (upper : int) =
    &(LENGTH
        (FILTER
          (\index : int. f index = value)
          (GENLIST
            (\offset : num. lower + &offset)
            (sc_to_num (upper - lower)))))`;

val sc_map_permut_def = Define `
  sc_map_permut
      (first_map : int -> int)
      (second_map : int -> int)
      (lower : int)
      (upper : int) <=>
    !value : int.
      sc_occurrences value first_map lower upper =
      sc_occurrences value second_map lower upper`;

val sc_column_def = Define `
  sc_column (m : sc_matrix) (j : int) =
    \i : int. sc_elts m i j`;

val sc_prefix_def = Define `
  sc_prefix
      (xs : int list)
      (m : sc_matrix)
      (j : int)
      (limit : int) <=>
    !k : int.
      (0 : int) <= k /\ k < limit ==>
      sc_get xs k = sc_elts m k j`;

val sc_unchanged_except_column_def = Define `
  sc_unchanged_except_column
      (current : sc_matrix)
      (original : sc_matrix)
      (j : int) <=>
    !k l : int.
      (((0 : int) <= k /\ k < sc_rows current) /\
       ((0 : int) <= l /\ l < sc_columns current) /\
       ~(l = j)) ==>
      sc_elts current k l = sc_elts original k l`;

val sc_list_sorted_def = Define `
  sc_list_sorted (xs : int list) <=>
    !i k : int.
      (0 : int) <= i /\ i <= k /\ k < &(LENGTH xs) ==>
      sc_get xs i <= sc_get xs k`;

val sc_column_sorted_def = Define `
  sc_column_sorted (m : sc_matrix) (j : int) <=>
    !i k : int.
      (0 : int) <= i /\ i <= k /\ k < sc_rows m ==>
      sc_elts m i j <= sc_elts m k j`;

val sc_matrix_update_def = Define `
  sc_matrix_update
      (elements : int -> int -> int)
      (i : int)
      (j : int)
      (value : int) =
    \row column.
      if row = i then
        if column = j then value else elements row column
      else
        elements row column`;

val sc_final_column_def = Define `
  sc_final_column
      (current : sc_matrix)
      (original : sc_matrix)
      (j : int) <=>
    sc_unchanged_except_column current original j /\
    sc_column_sorted current j /\
    sc_map_permut
      (sc_column current j)
      (sc_column original j)
      (0 : int)
      (sc_rows current)`;

val sc_write_step_vc_def = Define `
  sc_write_step_vc
      (xs : int list)
      (original : sc_matrix)
      (j : int)
      (current : sc_matrix)
      (last : int) <=>
    !i : int.
      (((0 : int) <= i /\ i <= last) /\
       sc_prefix xs current j i /\
       sc_unchanged_except_column current original j) ==>
      (((0 : int) <= i /\ i < &(LENGTH xs)) /\
       sc_valid_index current i j /\
       (!next : sc_matrix.
          sc_matrix_ok next ==>
          sc_dimensions next current ==>
          sc_elts next =
            sc_matrix_update
              (sc_elts current) i j (sc_get xs i) ==>
          sc_prefix xs next j (i + (1 : int)) /\
          sc_unchanged_except_column next original j))`;

val sc_write_loop_vc_def = Define `
  sc_write_loop_vc
      (xs : int list)
      (original : sc_matrix)
      (j : int)
      (current : sc_matrix)
      (last : int) <=>
    sc_write_step_vc xs original j current last /\
    ((sc_prefix xs current j (last + (1 : int)) /\
      sc_unchanged_except_column current original j) ==>
     sc_final_column current original j)`;

val sc_write_phase_vc_def = Define `
  sc_write_phase_vc
      (xs : int list)
      (original : sc_matrix)
      (j : int) <=>
    let last = sc_rows original - (1 : int)
    in
      (((0 : int) <= last + (1 : int) ==>
        sc_prefix xs original j (0 : int) /\
        (!current : sc_matrix.
           sc_matrix_ok current ==>
           sc_dimensions current original ==>
           sc_write_loop_vc xs original j current last)) /\
       (last + (1 : int) < (0 : int) ==>
        sc_final_column original original j))`;

val sc_read_update_vc_def = Define `
  sc_read_update_vc
      (m : sc_matrix)
      (j : int)
      (a1 : int list)
      (i : int) <=>
    sc_valid_index m i j /\
    (let value = sc_elts m i j
     in
       ((0 : int) <= i /\ i < &(LENGTH a1)) /\
       (LENGTH (LUPDATE value (sc_to_num i) a1) = LENGTH a1 ==>
        (\k : int. sc_get (LUPDATE value (sc_to_num i) a1) k) =
          sc_fun_update (sc_get a1) i value ==>
        sc_prefix
          (LUPDATE value (sc_to_num i) a1)
          m j (i + (1 : int))))`;

val sc_copy_and_sort_vc_def = Define `
  sc_copy_and_sort_vc
      (a : int list)
      (m : sc_matrix)
      (j : int) <=>
    let last = sc_rows m - (1 : int)
    in
      (((0 : int) <= last + (1 : int) ==>
        sc_prefix a m j (0 : int) /\
        (!a1 : int list.
           LENGTH a1 = LENGTH a ==>
           ((!i : int.
              (((0 : int) <= i /\ i <= last) /\
               sc_prefix a1 m j i) ==>
              sc_read_update_vc m j a1 i) /\
            (sc_prefix a1 m j (last + (1 : int)) ==>
             (!a2 : int list.
                LENGTH a2 = LENGTH a1 ==>
                sc_list_sorted a2 /\
                sc_map_permut
                  (sc_get a2)
                  (sc_get a1)
                  (0 : int)
                  (&(LENGTH a2)) ==>
                sc_write_phase_vc a2 m j))))) /\
       (last + (1 : int) < (0 : int) ==>
        (!a1 : int list.
           LENGTH a1 = LENGTH a ==>
           sc_list_sorted a1 /\
           sc_map_permut
             (sc_get a1)
             (sc_get a)
             (0 : int)
             (&(LENGTH a1)) ==>
           sc_write_phase_vc a1 m j)))`;

val verifythis_2021_shearsort_ShearSort_sort_columnqtvc_statement =
  ``!j : int.
    !m : sc_matrix.
      sc_matrix_ok m ==>
      (0 : int) <= j ==>
      j < sc_columns m ==>
      (0 : int) <= sc_rows m /\
      (!a : int list.
         ((!i : int.
            (0 : int) <= i /\ i < sc_rows m ==>
            sc_get a i = (0 : int)) /\
          &(LENGTH a) = sc_rows m) ==>
         sc_copy_and_sort_vc a m j)``;
