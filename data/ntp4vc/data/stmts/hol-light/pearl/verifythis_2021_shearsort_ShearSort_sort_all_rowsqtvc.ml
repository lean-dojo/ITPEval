(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc: the
  verification condition for sorting every row of an integer matrix in
  alternating ascending and descending order while preserving each row's
  multiset. This file contains no proof.
*)

let ntp4vc_sar_matrix_INDUCT, ntp4vc_sar_matrix_RECURSION =
  define_type
    "ntp4vc_sar_matrix =
       NTP4VCSARMatrix num num (int->int->int)";;

let ntp4vc_sar_rows =
  new_recursive_definition ntp4vc_sar_matrix_RECURSION
   `!r c e.
      ntp4vc_sar_rows (NTP4VCSARMatrix r c e) = (&r:int)`;;

let ntp4vc_sar_columns =
  new_recursive_definition ntp4vc_sar_matrix_RECURSION
   `!r c e.
      ntp4vc_sar_columns (NTP4VCSARMatrix r c e) = (&c:int)`;;

let ntp4vc_sar_elts =
  new_recursive_definition ntp4vc_sar_matrix_RECURSION
   `!r c e.
      ntp4vc_sar_elts (NTP4VCSARMatrix r c e) = e`;;

let ntp4vc_sar_cdiv = new_definition
 `ntp4vc_sar_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let ntp4vc_sar_cmod = new_definition
 `ntp4vc_sar_cmod (n:int) (d:int) =
    n - d * ntp4vc_sar_cdiv n d`;;

let ntp4vc_sar_same_dimensions = new_definition
 `ntp4vc_sar_same_dimensions
    (left:ntp4vc_sar_matrix)
    (right:ntp4vc_sar_matrix) <=>
    ntp4vc_sar_rows left = ntp4vc_sar_rows right /\
    ntp4vc_sar_columns left = ntp4vc_sar_columns right`;;

let ntp4vc_sar_permut = new_definition
 `ntp4vc_sar_permut
    (left:int->int) (right:int->int) (lower:int) (upper:int) <=>
    !value:int.
      CARD {index:int |
              lower <= index /\ index < upper /\ left index = value} =
      CARD {index:int |
              lower <= index /\ index < upper /\ right index = value}`;;

let ntp4vc_sar_all_rows_permuted = new_definition
 `ntp4vc_sar_all_rows_permuted
    (current:ntp4vc_sar_matrix)
    (original:ntp4vc_sar_matrix) <=>
    !i:int.
      (&0:int) <= i /\ i < ntp4vc_sar_rows current
      ==>
      ntp4vc_sar_permut
        (ntp4vc_sar_elts current i)
        (ntp4vc_sar_elts original i)
        (&0:int)
        (ntp4vc_sar_columns current)`;;

let ntp4vc_sar_rows_sorted_before = new_definition
 `ntp4vc_sar_rows_sorted_before
    (current:ntp4vc_sar_matrix) (limit:int) <=>
    !i j k:int.
      (((&0:int) <= i /\ i < limit) /\
       (&0:int) <= j /\ j <= k /\ k < ntp4vc_sar_columns current)
      ==>
      if ntp4vc_sar_cmod i (&2:int) = (&0:int)
      then ntp4vc_sar_elts current i j <= ntp4vc_sar_elts current i k
      else ntp4vc_sar_elts current i k <= ntp4vc_sar_elts current i j`;;

let ntp4vc_sar_other_rows_unchanged = new_definition
 `ntp4vc_sar_other_rows_unchanged
    (current:ntp4vc_sar_matrix)
    (previous:ntp4vc_sar_matrix)
    (tid:int) <=>
    !j k:int.
      ((&0:int) <= j /\ j < ntp4vc_sar_rows current /\
       ((&0:int) <= k /\ k < ntp4vc_sar_columns current) /\
       ~(j = tid))
      ==>
      ntp4vc_sar_elts current j k = ntp4vc_sar_elts previous j k`;;

let ntp4vc_sar_selected_row_sorted = new_definition
 `ntp4vc_sar_selected_row_sorted
    (current:ntp4vc_sar_matrix) (tid:int) <=>
    !j k:int.
      (&0:int) <= j /\ j <= k /\ k < ntp4vc_sar_columns current
      ==>
      if ntp4vc_sar_cmod tid (&2:int) = (&0:int)
      then ntp4vc_sar_elts current tid j <= ntp4vc_sar_elts current tid k
      else ntp4vc_sar_elts current tid k <= ntp4vc_sar_elts current tid j`;;

let ntp4vc_sar_selected_row_permuted = new_definition
 `ntp4vc_sar_selected_row_permuted
    (current:ntp4vc_sar_matrix)
    (previous:ntp4vc_sar_matrix)
    (tid:int) <=>
    ntp4vc_sar_permut
      (ntp4vc_sar_elts current tid)
      (ntp4vc_sar_elts previous tid)
      (&0:int)
      (ntp4vc_sar_columns current)`;;

let ntp4vc_sar_sort_row_post = new_definition
 `ntp4vc_sar_sort_row_post
    (current:ntp4vc_sar_matrix)
    (previous:ntp4vc_sar_matrix)
    (tid:int) <=>
    ntp4vc_sar_other_rows_unchanged current previous tid /\
    ntp4vc_sar_selected_row_sorted current tid /\
    ntp4vc_sar_selected_row_permuted current previous tid`;;

let ntp4vc_sar_loop_step_post = new_definition
 `ntp4vc_sar_loop_step_post
    (current:ntp4vc_sar_matrix)
    (original:ntp4vc_sar_matrix)
    (tid:int) <=>
    ntp4vc_sar_all_rows_permuted current original /\
    ntp4vc_sar_rows_sorted_before current (tid + (&1:int))`;;

let ntp4vc_sar_all_sort_row_results = new_definition
 `ntp4vc_sar_all_sort_row_results
    (previous:ntp4vc_sar_matrix)
    (original:ntp4vc_sar_matrix)
    (tid:int) <=>
    !current:ntp4vc_sar_matrix.
      ntp4vc_sar_same_dimensions current previous
      ==>
      ntp4vc_sar_sort_row_post current previous tid
      ==>
      ntp4vc_sar_loop_step_post current original tid`;;

let ntp4vc_sar_loop_iterations = new_definition
 `ntp4vc_sar_loop_iterations
    (current:ntp4vc_sar_matrix)
    (original:ntp4vc_sar_matrix)
    (upper:int) <=>
    !tid:int.
      (((&0:int) <= tid /\ tid <= upper) /\
       ntp4vc_sar_all_rows_permuted current original /\
       ntp4vc_sar_rows_sorted_before current tid)
      ==>
      ~((&2:int) = (&0:int)) /\
      ((&0:int) <= tid /\ tid < ntp4vc_sar_rows current) /\
      ntp4vc_sar_all_sort_row_results current original tid`;;

let ntp4vc_sar_final_contract = new_definition
 `ntp4vc_sar_final_contract
    (current:ntp4vc_sar_matrix)
    (original:ntp4vc_sar_matrix) <=>
    ntp4vc_sar_all_rows_permuted current original /\
    ntp4vc_sar_rows_sorted_before current (ntp4vc_sar_rows current)`;;

let ntp4vc_sar_loop_completion = new_definition
 `ntp4vc_sar_loop_completion
    (current:ntp4vc_sar_matrix)
    (original:ntp4vc_sar_matrix)
    (upper:int) <=>
    (ntp4vc_sar_all_rows_permuted current original /\
     ntp4vc_sar_rows_sorted_before current (upper + (&1:int)))
    ==>
    ntp4vc_sar_final_contract current original`;;

let ntp4vc_sar_all_loop_matrices = new_definition
 `ntp4vc_sar_all_loop_matrices
    (original:ntp4vc_sar_matrix) (upper:int) <=>
    !current:ntp4vc_sar_matrix.
      ntp4vc_sar_same_dimensions current original
      ==>
      ntp4vc_sar_loop_iterations current original upper /\
      ntp4vc_sar_loop_completion current original upper`;;

let ntp4vc_sar_initial_invariant = new_definition
 `ntp4vc_sar_initial_invariant (original:ntp4vc_sar_matrix) <=>
    ntp4vc_sar_all_rows_permuted original original /\
    ntp4vc_sar_rows_sorted_before original (&0:int)`;;

let statement =
 `!original:ntp4vc_sar_matrix.
    let upper = ntp4vc_sar_rows original - (&1:int) in
    (((&0:int) <= upper + (&1:int)
      ==>
      ntp4vc_sar_initial_invariant original /\
      ntp4vc_sar_all_loop_matrices original upper) /\
     (upper + (&1:int) < (&0:int)
      ==>
      ntp4vc_sar_final_contract original original))`;;
