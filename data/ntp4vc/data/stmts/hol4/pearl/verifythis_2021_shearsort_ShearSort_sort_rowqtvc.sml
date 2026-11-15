(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_rowqtvc: the full
  verification condition for copying, sorting, optionally reversing, and
  writing back one row of an integer matrix while preserving all other rows
  and the selected row's multiset. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val _ = type_abbrev
  ("sr_matrix", ``:int # (int # (int -> int -> int))``);

val sr_to_num_def = Define `
  sr_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sr_rows_def = Define `
  sr_rows (m : sr_matrix) = FST m`;

val sr_columns_def = Define `
  sr_columns (m : sr_matrix) = FST (SND m)`;

val sr_elts_def = Define `
  sr_elts (m : sr_matrix) = SND (SND m)`;

val sr_matrix_ok_def = Define `
  sr_matrix_ok (m : sr_matrix) <=>
    (0 : int) <= sr_rows m /\ (0 : int) <= sr_columns m`;

val sr_dimensions_def = Define `
  sr_dimensions (current : sr_matrix) (previous : sr_matrix) <=>
    sr_rows current = sr_rows previous /\
    sr_columns current = sr_columns previous`;

val sr_valid_index_def = Define `
  sr_valid_index (m : sr_matrix) (i : int) (j : int) <=>
    ((0 : int) <= i /\ i < sr_rows m) /\
    (0 : int) <= j /\ j < sr_columns m`;

val sr_get_def = Define `
  sr_get (xs : int list) (i : int) =
    if sr_to_num i < LENGTH xs then EL (sr_to_num i) xs else (0 : int)`;

val sr_fun_update_def = Define `
  sr_fun_update (f : 'a -> 'b) (key : 'a) (value : 'b) =
    \query. if query = key then value else f query`;

val sr_occurrences_def = Define `
  sr_occurrences
      (value : int)
      (f : int -> int)
      (lower : int)
      (upper : int) =
    &(LENGTH
        (FILTER
          (\index : int. f index = value)
          (GENLIST
            (\offset : num. lower + &offset)
            (sr_to_num (upper - lower)))))`;

val sr_map_permut_def = Define `
  sr_map_permut
      (first_map : int -> int)
      (second_map : int -> int)
      (lower : int)
      (upper : int) <=>
    !value : int.
      sr_occurrences value first_map lower upper =
      sr_occurrences value second_map lower upper`;

val sr_prefix_def = Define `
  sr_prefix
      (xs : int list)
      (m : sr_matrix)
      (i : int)
      (upper : int) <=>
    !k : int.
      (0 : int) <= k /\ k < upper ==>
      sr_get xs k = sr_elts m i k`;

val sr_other_rows_def = Define `
  sr_other_rows
      (current : sr_matrix)
      (original : sr_matrix)
      (i : int) <=>
    !k l : int.
      (((0 : int) <= k /\ k < sr_rows current) /\
       ((0 : int) <= l /\ l < sr_columns current) /\
       ~(k = i)) ==>
      sr_elts current k l = sr_elts original k l`;

val sr_row_sorted_def = Define `
  sr_row_sorted
      (m : sr_matrix)
      (i : int)
      (ascending : bool) <=>
    !j k : int.
      (0 : int) <= j /\ j <= k /\ k < sr_columns m ==>
      if ascending then
        sr_elts m i j <= sr_elts m i k
      else
        sr_elts m i k <= sr_elts m i j`;

val sr_row_permuted_def = Define `
  sr_row_permuted
      (current : sr_matrix)
      (original : sr_matrix)
      (i : int) <=>
    sr_map_permut
      (sr_elts current i)
      (sr_elts original i)
      (0 : int)
      (sr_columns current)`;

val sr_post_def = Define `
  sr_post
      (current : sr_matrix)
      (original : sr_matrix)
      (i : int)
      (ascending : bool) <=>
    sr_other_rows current original i /\
    sr_row_sorted current i ascending /\
    sr_row_permuted current original i`;

val sr_list_sorted_def = Define `
  sr_list_sorted (xs : int list) <=>
    !i j : int.
      (0 : int) <= i /\ i <= j /\ j < &(LENGTH xs) ==>
      sr_get xs i <= sr_get xs j`;

val sr_list_permuted_def = Define `
  sr_list_permuted
      (current : int list)
      (previous : int list) <=>
    sr_map_permut
      (sr_get current)
      (sr_get previous)
      (0 : int)
      (&(LENGTH current))`;

val sr_matrix_update_def = Define `
  sr_matrix_update
      (elements : int -> int -> int)
      (i : int)
      (j : int)
      (value : int) =
    \row column.
      if row = i then
        if column = j then value else elements row column
      else
        elements row column`;

val sr_write_iteration_def = Define `
  sr_write_iteration
      (xs : int list)
      (original : sr_matrix)
      (i : int)
      (ascending : bool)
      (upper : int)
      (current : sr_matrix) <=>
    (!j : int.
       (((0 : int) <= j /\ j <= upper) /\
        sr_prefix xs current i j /\
        sr_other_rows current original i) ==>
       (((0 : int) <= j /\ j < &(LENGTH xs)) /\
        sr_valid_index current i j /\
        (!next : sr_matrix.
           sr_matrix_ok next ==>
           sr_dimensions next current ==>
           sr_elts next =
             sr_matrix_update
               (sr_elts current) i j (sr_get xs j) ==>
           sr_prefix xs next i (j + (1 : int)) /\
           sr_other_rows next original i))) /\
    ((sr_prefix xs current i (upper + (1 : int)) /\
      sr_other_rows current original i) ==>
     sr_post current original i ascending)`;

val sr_write_loop_def = Define `
  sr_write_loop
      (xs : int list)
      (original : sr_matrix)
      (i : int)
      (ascending : bool) <=>
    let upper = sr_columns original - (1 : int)
    in
      (((0 : int) <= upper + (1 : int) ==>
        sr_prefix xs original i (0 : int) /\
        (!current : sr_matrix.
           sr_matrix_ok current ==>
           sr_dimensions current original ==>
           sr_write_iteration
             xs original i ascending upper current)) /\
       (upper + (1 : int) < (0 : int) ==>
        sr_post original original i ascending))`;

val sr_reverse_initial_def = Define `
  sr_reverse_initial (base : int list) <=>
    let upper = &(LENGTH base) - (1 : int)
    in
      ((((0 : int) <= (0 : int) /\
         (0 : int) <= upper + (1 : int)) /\
        upper + (1 : int) <= &(LENGTH base)) /\
       (0 : int) + upper = &(LENGTH base) - (1 : int) /\
       (!j : int.
          ((0 : int) <= j /\ j < (0 : int)) \/
          (upper < j /\ j < &(LENGTH base)) ==>
          sr_get base j =
            sr_get base (&(LENGTH base) - (1 : int) - j)) /\
       sr_map_permut
         (sr_get base)
         (sr_get base)
         (0 : int)
         (&(LENGTH base)))`;

val sr_reverse_invariant_def = Define `
  sr_reverse_invariant
      (base : int list)
      (current : int list)
      (u : int)
      (v : int) <=>
    (((0 : int) <= u /\
      u <= v + (1 : int)) /\
     v + (1 : int) <= &(LENGTH current)) /\
    u + v = &(LENGTH current) - (1 : int) /\
    (!j : int.
       u <= j /\ j <= v ==>
       sr_get current j = sr_get base j) /\
    (!j : int.
       ((0 : int) <= j /\ j < u) \/
       (v < j /\ j < &(LENGTH current)) ==>
       sr_get current j =
         sr_get base (&(LENGTH current) - (1 : int) - j)) /\
    sr_map_permut
      (sr_get base)
      (sr_get current)
      (0 : int)
      (&(LENGTH current))`;

val sr_swap_effect_def = Define `
  sr_swap_effect
      (before : int list)
      (after : int list)
      (u : int)
      (v : int) <=>
    let size = &(LENGTH after)
    in
      ((((0 : int) <= u /\ u < size) /\
        (0 : int) <= v /\ v < size) /\
       (!index : int.
          (((0 : int) <= index /\ index <= size) /\
           ~(index = u) /\ ~(index = v)) ==>
          sr_get after index = sr_get before index) /\
       sr_get after u = sr_get before v /\
       sr_get after v = sr_get before u)`;

val sr_reverse_step_post_def = Define `
  sr_reverse_step_post
      (base : int list)
      (current : int list)
      (u : int)
      (v : int) <=>
    ((0 : int) <= v - u /\
     v - (1 : int) - (u + (1 : int)) < v - u) /\
    sr_reverse_invariant
      base current (u + (1 : int)) (v - (1 : int))`;

val sr_swap_case_def = Define `
  sr_swap_case
      (base : int list)
      (current : int list)
      (u : int)
      (v : int) <=>
    ((0 : int) <= v /\ v < &(LENGTH current)) /\
    (let temporary = sr_get current v
     in
       ((0 : int) <= u /\ u < &(LENGTH current)) /\
       (let old_u = sr_get current u
        in
          ((0 : int) <= v /\ v < &(LENGTH current)) /\
          (let at_v = LUPDATE old_u (sr_to_num v) current
           in
             LENGTH at_v = LENGTH current ==>
             (\index : int. sr_get at_v index) =
               sr_fun_update (sr_get current) v old_u ==>
             ((0 : int) <= u /\ u < &(LENGTH at_v)) /\
             (let swapped =
                LUPDATE temporary (sr_to_num u) at_v
              in
                LENGTH swapped = LENGTH at_v ==>
                (\index : int. sr_get swapped index) =
                  sr_fun_update (sr_get at_v) u temporary ==>
                sr_swap_effect current swapped u v /\
                (sr_map_permut
                   (sr_get swapped)
                   (sr_get current)
                   (0 : int)
                   (&(LENGTH swapped)) ==>
                 sr_reverse_step_post base swapped u v)))))`;

val sr_reverse_loop_def = Define `
  sr_reverse_loop
      (base : int list)
      (original : sr_matrix)
      (i : int)
      (ascending : bool) <=>
    sr_reverse_initial base /\
    (!v u : int.
       !current : int list.
         LENGTH current = LENGTH base ==>
         sr_reverse_invariant base current u v ==>
         if u < v then
           sr_swap_case base current u v
         else
           sr_write_loop current original i ascending)`;

val sr_after_sort_def = Define `
  sr_after_sort
      (sorted : int list)
      (original : sr_matrix)
      (i : int)
      (ascending : bool) <=>
    if ~ascending then
      sr_reverse_loop sorted original i ascending
    else
      sr_write_loop sorted original i ascending`;

val sr_read_iteration_def = Define `
  sr_read_iteration
      (initial : int list)
      (original : sr_matrix)
      (i : int)
      (ascending : bool)
      (upper : int)
      (current : int list) <=>
    (!j : int.
       (((0 : int) <= j /\ j <= upper) /\
        sr_prefix current original i j) ==>
       sr_valid_index original i j /\
       (let value = sr_elts original i j
        in
          ((0 : int) <= j /\ j < &(LENGTH current)) /\
          (LENGTH (LUPDATE value (sr_to_num j) current) =
             LENGTH current ==>
           (\index : int.
              sr_get
                (LUPDATE value (sr_to_num j) current)
                index) =
             sr_fun_update (sr_get current) j value ==>
           sr_prefix
             (LUPDATE value (sr_to_num j) current)
             original i (j + (1 : int))))) /\
    (sr_prefix current original i (upper + (1 : int)) ==>
     (!sorted : int list.
        LENGTH sorted = LENGTH current ==>
        sr_list_sorted sorted /\
        sr_list_permuted sorted current ==>
        sr_after_sort sorted original i ascending))`;

val sr_read_loop_def = Define `
  sr_read_loop
      (initial : int list)
      (original : sr_matrix)
      (i : int)
      (ascending : bool) <=>
    let upper = sr_columns original - (1 : int)
    in
      (((0 : int) <= upper + (1 : int) ==>
        sr_prefix initial original i (0 : int) /\
        (!current : int list.
           LENGTH current = LENGTH initial ==>
           sr_read_iteration
             initial original i ascending upper current)) /\
       (upper + (1 : int) < (0 : int) ==>
        (!sorted : int list.
           LENGTH sorted = LENGTH initial ==>
           sr_list_sorted sorted /\
           sr_list_permuted sorted initial ==>
           sr_after_sort sorted original i ascending)))`;

val verifythis_2021_shearsort_ShearSort_sort_rowqtvc_statement =
  ``!i : int.
    !m : sr_matrix.
    !ascending : bool.
      sr_matrix_ok m ==>
      (0 : int) <= i ==>
      i < sr_rows m ==>
      (0 : int) <= sr_columns m /\
      (!initial : int list.
         ((!j : int.
            (0 : int) <= j /\ j < sr_columns m ==>
            sr_get initial j = (0 : int)) /\
          &(LENGTH initial) = sr_columns m) ==>
         sr_read_loop initial m i ascending)``;
