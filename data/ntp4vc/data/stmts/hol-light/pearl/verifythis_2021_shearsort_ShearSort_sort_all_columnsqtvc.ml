(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_all_columnsqtvc: the full
  verification condition for sorting every column of an integer matrix,
  either directly or by transposing, sorting rows, and transposing back.
  This file contains no proof.
*)

let shearsort_sac_rows = new_definition
 `shearsort_sac_rows
    (m:(int#int)#(int->int->int)) = FST (FST m)`;;

let shearsort_sac_columns = new_definition
 `shearsort_sac_columns
    (m:(int#int)#(int->int->int)) = SND (FST m)`;;

let shearsort_sac_elts = new_definition
 `shearsort_sac_elts
    (m:(int#int)#(int->int->int)) (i:int) (j:int) = SND m i j`;;

let shearsort_sac_matrix = new_definition
 `shearsort_sac_matrix (m:(int#int)#(int->int->int)) <=>
    (&0:int) <= shearsort_sac_rows m /\
    (&0:int) <= shearsort_sac_columns m`;;

let shearsort_sac_dimensions = new_definition
 `shearsort_sac_dimensions
    (current:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int)) <=>
    shearsort_sac_rows current = shearsort_sac_rows previous /\
    shearsort_sac_columns current = shearsort_sac_columns previous`;;

let shearsort_sac_square = new_definition
 `shearsort_sac_square (m:(int#int)#(int->int->int)) <=>
    shearsort_sac_rows m = shearsort_sac_columns m`;;

let shearsort_sac_column = new_definition
 `shearsort_sac_column
    (m:(int#int)#(int->int->int)) (j:int) (i:int) =
    shearsort_sac_elts m i j`;;

let shearsort_sac_permut = new_definition
 `shearsort_sac_permut
    (first:int->int) (second:int->int) (lower:int) (upper:int) <=>
    !value:int.
      CARD {index:int |
              lower <= index /\ index < upper /\ first index = value} =
      CARD {index:int |
              lower <= index /\ index < upper /\ second index = value}`;;

let shearsort_sac_column_permuted_to = new_definition
 `shearsort_sac_column_permuted_to
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int)) <=>
    !j:int.
      (&0:int) <= j /\ j < shearsort_sac_columns current
      ==>
      shearsort_sac_permut
        (shearsort_sac_column current j)
        (shearsort_sac_column original j)
        (&0:int)
        (shearsort_sac_rows current)`;;

let shearsort_sac_columns_sorted_before = new_definition
 `shearsort_sac_columns_sorted_before
    (current:(int#int)#(int->int->int)) (limit:int) <=>
    !i j k:int.
      (((&0:int) <= i /\ i <= k /\ k < shearsort_sac_rows current) /\
       (&0:int) <= j /\ j < limit)
      ==>
      shearsort_sac_elts current i j <=
      shearsort_sac_elts current k j`;;

let shearsort_sac_column_post = new_definition
 `shearsort_sac_column_post
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int)) <=>
    shearsort_sac_column_permuted_to current original /\
    shearsort_sac_columns_sorted_before
      current (shearsort_sac_columns current)`;;

let shearsort_sac_other_columns_unchanged = new_definition
 `shearsort_sac_other_columns_unchanged
    (current:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int))
    (tid:int) <=>
    !i k:int.
      ((&0:int) <= i /\ i < shearsort_sac_rows current /\
       ((&0:int) <= k /\ k < shearsort_sac_columns current) /\
       ~(k = tid))
      ==>
      shearsort_sac_elts current i k =
      shearsort_sac_elts previous i k`;;

let shearsort_sac_selected_column_sorted = new_definition
 `shearsort_sac_selected_column_sorted
    (current:(int#int)#(int->int->int)) (tid:int) <=>
    !i k:int.
      (&0:int) <= i /\ i <= k /\ k < shearsort_sac_rows current
      ==>
      shearsort_sac_elts current i tid <=
      shearsort_sac_elts current k tid`;;

let shearsort_sac_selected_column_permuted = new_definition
 `shearsort_sac_selected_column_permuted
    (current:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int))
    (tid:int) <=>
    shearsort_sac_permut
      (shearsort_sac_column current tid)
      (shearsort_sac_column previous tid)
      (&0:int)
      (shearsort_sac_rows current)`;;

let shearsort_sac_column_iteration_result = new_definition
 `shearsort_sac_column_iteration_result
    (original:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int))
    (tid:int)
    (current:(int#int)#(int->int->int)) <=>
    (shearsort_sac_other_columns_unchanged current previous tid /\
     shearsort_sac_selected_column_sorted current tid /\
     shearsort_sac_selected_column_permuted current previous tid)
    ==>
    shearsort_sac_column_permuted_to current original /\
    shearsort_sac_columns_sorted_before current (tid + (&1:int))`;;

let shearsort_sac_column_iteration = new_definition
 `shearsort_sac_column_iteration
    (original:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int))
    (tid:int) <=>
    ((&0:int) <= tid /\ tid < shearsort_sac_columns previous) /\
    (!current:(int#int)#(int->int->int).
       shearsort_sac_matrix current /\
       shearsort_sac_dimensions current previous
       ==>
       shearsort_sac_column_iteration_result
         original previous tid current)`;;

let shearsort_sac_column_loop_iterations = new_definition
 `shearsort_sac_column_loop_iterations
    (original:(int#int)#(int->int->int))
    (current:(int#int)#(int->int->int))
    (upper:int) <=>
    !tid:int.
      (((&0:int) <= tid /\ tid <= upper) /\
       shearsort_sac_column_permuted_to current original /\
       shearsort_sac_columns_sorted_before current tid)
      ==>
      shearsort_sac_column_iteration original current tid`;;

let shearsort_sac_column_loop_completion = new_definition
 `shearsort_sac_column_loop_completion
    (original:(int#int)#(int->int->int))
    (current:(int#int)#(int->int->int))
    (upper:int) <=>
    (shearsort_sac_column_permuted_to current original /\
     shearsort_sac_columns_sorted_before current (upper + (&1:int)))
    ==>
    shearsort_sac_column_post current original`;;

let shearsort_sac_column_loop_vc = new_definition
 `shearsort_sac_column_loop_vc
    (original:(int#int)#(int->int->int))
    (initial:(int#int)#(int->int->int))
    (upper:int) <=>
    !current:(int#int)#(int->int->int).
      shearsort_sac_matrix current /\
      shearsort_sac_dimensions current initial
      ==>
      shearsort_sac_column_loop_iterations original current upper /\
      shearsort_sac_column_loop_completion original current upper`;;

let shearsort_sac_direct_column_branch = new_definition
 `shearsort_sac_direct_column_branch
    (original:(int#int)#(int->int->int)) <=>
    let upper = shearsort_sac_columns original - (&1:int) in
    (((&0:int) <= upper + (&1:int)
      ==>
      (shearsort_sac_column_permuted_to original original /\
       shearsort_sac_columns_sorted_before original (&0:int)) /\
      shearsort_sac_column_loop_vc original original upper) /\
     (upper + (&1:int) < (&0:int)
      ==>
      shearsort_sac_column_post original original))`;;

let shearsort_sac_transpose_relation = new_definition
 `shearsort_sac_transpose_relation
    (before:(int#int)#(int->int->int))
    (after:(int#int)#(int->int->int)) <=>
    !i j:int.
      (((&0:int) <= i /\ i < shearsort_sac_rows after) /\
       (&0:int) <= j /\ j < shearsort_sac_columns after)
      ==>
      shearsort_sac_elts before i j =
      shearsort_sac_elts after j i`;;

let shearsort_sac_rows_permuted_from_columns = new_definition
 `shearsort_sac_rows_permuted_from_columns
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int))
    (n:int) <=>
    !j:int.
      (&0:int) <= j /\ j < n
      ==>
      shearsort_sac_permut
        (shearsort_sac_elts current j)
        (shearsort_sac_column original j)
        (&0:int)
        n`;;

let shearsort_sac_rows_sorted_before = new_definition
 `shearsort_sac_rows_sorted_before
    (current:(int#int)#(int->int->int))
    (n:int)
    (limit:int) <=>
    !i j k:int.
      (((&0:int) <= i /\ i <= k /\ k < n) /\
       (&0:int) <= j /\ j < limit)
      ==>
      shearsort_sac_elts current j i <=
      shearsort_sac_elts current j k`;;

let shearsort_sac_other_rows_unchanged = new_definition
 `shearsort_sac_other_rows_unchanged
    (current:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int))
    (tid:int) <=>
    !j k:int.
      ((&0:int) <= j /\ j < shearsort_sac_rows current /\
       ((&0:int) <= k /\ k < shearsort_sac_columns current) /\
       ~(j = tid))
      ==>
      shearsort_sac_elts current j k =
      shearsort_sac_elts previous j k`;;

let shearsort_sac_selected_row_sorted = new_definition
 `shearsort_sac_selected_row_sorted
    (current:(int#int)#(int->int->int)) (tid:int) <=>
    !j k:int.
      (&0:int) <= j /\ j <= k /\ k < shearsort_sac_columns current
      ==>
      shearsort_sac_elts current tid j <=
      shearsort_sac_elts current tid k`;;

let shearsort_sac_selected_row_permuted = new_definition
 `shearsort_sac_selected_row_permuted
    (current:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int))
    (tid:int) <=>
    shearsort_sac_permut
      (shearsort_sac_elts current tid)
      (shearsort_sac_elts previous tid)
      (&0:int)
      (shearsort_sac_columns current)`;;

let shearsort_sac_row_iteration_result = new_definition
 `shearsort_sac_row_iteration_result
    (original:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int))
    (n:int)
    (tid:int)
    (current:(int#int)#(int->int->int)) <=>
    (shearsort_sac_other_rows_unchanged current previous tid /\
     shearsort_sac_selected_row_sorted current tid /\
     shearsort_sac_selected_row_permuted current previous tid)
    ==>
    shearsort_sac_rows_permuted_from_columns current original n /\
    shearsort_sac_rows_sorted_before current n (tid + (&1:int))`;;

let shearsort_sac_row_iteration = new_definition
 `shearsort_sac_row_iteration
    (original:(int#int)#(int->int->int))
    (previous:(int#int)#(int->int->int))
    (n:int)
    (tid:int) <=>
    ((&0:int) <= tid /\ tid < shearsort_sac_rows previous) /\
    (!current:(int#int)#(int->int->int).
       shearsort_sac_matrix current /\
       shearsort_sac_dimensions current previous
       ==>
       shearsort_sac_row_iteration_result
         original previous n tid current)`;;

let shearsort_sac_row_loop_iterations = new_definition
 `shearsort_sac_row_loop_iterations
    (original:(int#int)#(int->int->int))
    (current:(int#int)#(int->int->int))
    (n:int)
    (upper:int) <=>
    !tid:int.
      (((&0:int) <= tid /\ tid <= upper) /\
       shearsort_sac_rows_permuted_from_columns current original n /\
       shearsort_sac_rows_sorted_before current n tid)
      ==>
      shearsort_sac_row_iteration original current n tid`;;

let shearsort_sac_transpose_back_post = new_definition
 `shearsort_sac_transpose_back_post
    (original:(int#int)#(int->int->int))
    (row_sorted:(int#int)#(int->int->int)) <=>
    shearsort_sac_square row_sorted /\
    (!transposed_back:(int#int)#(int->int->int).
       shearsort_sac_matrix transposed_back /\
       shearsort_sac_dimensions transposed_back row_sorted
       ==>
       shearsort_sac_transpose_relation row_sorted transposed_back
       ==>
       shearsort_sac_column_post transposed_back original)`;;

let shearsort_sac_row_loop_completion = new_definition
 `shearsort_sac_row_loop_completion
    (original:(int#int)#(int->int->int))
    (current:(int#int)#(int->int->int))
    (n:int)
    (upper:int) <=>
    (shearsort_sac_rows_permuted_from_columns current original n /\
     shearsort_sac_rows_sorted_before current n (upper + (&1:int)))
    ==>
    shearsort_sac_transpose_back_post original current`;;

let shearsort_sac_row_loop_vc = new_definition
 `shearsort_sac_row_loop_vc
    (original:(int#int)#(int->int->int))
    (initial:(int#int)#(int->int->int))
    (n:int)
    (upper:int) <=>
    !current:(int#int)#(int->int->int).
      shearsort_sac_matrix current /\
      shearsort_sac_dimensions current initial
      ==>
      shearsort_sac_row_loop_iterations original current n upper /\
      shearsort_sac_row_loop_completion original current n upper`;;

let shearsort_sac_empty_transpose_loop = new_definition
 `shearsort_sac_empty_transpose_loop
    (original:(int#int)#(int->int->int))
    (transposed:(int#int)#(int->int->int)) <=>
    shearsort_sac_square transposed /\
    (!transposed_back:(int#int)#(int->int->int).
       shearsort_sac_matrix transposed_back /\
       shearsort_sac_dimensions transposed_back transposed
       ==>
       shearsort_sac_transpose_relation transposed transposed_back
       ==>
       shearsort_sac_column_post transposed_back original)`;;

let shearsort_sac_transpose_loop_branch = new_definition
 `shearsort_sac_transpose_loop_branch
    (original:(int#int)#(int->int->int))
    (transposed:(int#int)#(int->int->int))
    (n:int) <=>
    let upper = shearsort_sac_columns transposed - (&1:int) in
    (((&0:int) <= upper + (&1:int)
      ==>
      (shearsort_sac_rows_permuted_from_columns
         transposed original n /\
       shearsort_sac_rows_sorted_before transposed n (&0:int)) /\
      shearsort_sac_row_loop_vc original transposed n upper) /\
     (upper + (&1:int) < (&0:int)
      ==>
      shearsort_sac_empty_transpose_loop original transposed))`;;

let shearsort_sac_transpose_column_branch = new_definition
 `shearsort_sac_transpose_column_branch
    (original:(int#int)#(int->int->int)) <=>
    let n = shearsort_sac_rows original in
    shearsort_sac_square original /\
    (!transposed:(int#int)#(int->int->int).
       shearsort_sac_matrix transposed /\
       shearsort_sac_dimensions transposed original
       ==>
       shearsort_sac_transpose_relation original transposed
       ==>
       shearsort_sac_transpose_loop_branch original transposed n)`;;

let statement =
 `!original:(int#int)#(int->int->int).
    shearsort_sac_matrix original
    ==>
    ((?result:bool.
        result = T \/ shearsort_sac_square original) /\
     (!choice:bool.
        choice = T \/ shearsort_sac_square original
        ==>
        if choice
        then shearsort_sac_direct_column_branch original
        else shearsort_sac_transpose_column_branch original))`;;
