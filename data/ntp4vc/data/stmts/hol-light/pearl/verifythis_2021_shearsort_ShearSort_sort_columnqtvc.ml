(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_columnqtvc: the full
  verification condition for copying, sorting, and writing back one column
  of an integer matrix while preserving all other columns and the selected
  column's multiset. This file contains no proof.
*)

let ntp4vc_sc_rows = new_definition
 `ntp4vc_sc_rows
    (m:(int#int)#(int->int->int)) = FST (FST m)`;;

let ntp4vc_sc_columns = new_definition
 `ntp4vc_sc_columns
    (m:(int#int)#(int->int->int)) = SND (FST m)`;;

let ntp4vc_sc_elts = new_definition
 `ntp4vc_sc_elts
    (m:(int#int)#(int->int->int)) (i:int) (j:int) = SND m i j`;;

let ntp4vc_sc_matrix = new_definition
 `ntp4vc_sc_matrix (m:(int#int)#(int->int->int)) <=>
    (&0:int) <= ntp4vc_sc_rows m /\
    (&0:int) <= ntp4vc_sc_columns m`;;

let ntp4vc_sc_same_dimensions = new_definition
 `ntp4vc_sc_same_dimensions
    (m1:(int#int)#(int->int->int))
    (m2:(int#int)#(int->int->int)) <=>
    ntp4vc_sc_rows m1 = ntp4vc_sc_rows m2 /\
    ntp4vc_sc_columns m1 = ntp4vc_sc_columns m2`;;

let ntp4vc_sc_valid_index = new_definition
 `ntp4vc_sc_valid_index
    (m:(int#int)#(int->int->int)) (i:int) (j:int) <=>
    ((&0:int) <= i /\ i < ntp4vc_sc_rows m) /\
    (&0:int) <= j /\ j < ntp4vc_sc_columns m`;;

let ntp4vc_sc_column = new_definition
 `ntp4vc_sc_column
    (m:(int#int)#(int->int->int)) (j:int) (i:int) =
    ntp4vc_sc_elts m i j`;;

let ntp4vc_sc_to_num = new_definition
 `ntp4vc_sc_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sc_nth = new_definition
 `ntp4vc_sc_nth (a:int list) (i:int) =
    if i < (&0:int) then (&0:int)
    else if ntp4vc_sc_to_num i < LENGTH a
    then EL (ntp4vc_sc_to_num i) a
    else (&0:int)`;;

let ntp4vc_sc_update =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:int.
       ntp4vc_sc_update ([]:int list) n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       ntp4vc_sc_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (ntp4vc_sc_update t (PRE n) x))`;;

let ntp4vc_sc_permut = new_definition
 `ntp4vc_sc_permut
    (first:int->int) (second:int->int) (lower:int) (upper:int) <=>
    !value:int.
      CARD {index:int |
              lower <= index /\ index < upper /\ first index = value} =
      CARD {index:int |
              lower <= index /\ index < upper /\ second index = value}`;;

let ntp4vc_sc_prefix = new_definition
 `ntp4vc_sc_prefix
    (a:int list)
    (m:(int#int)#(int->int->int))
    (j:int) (upper:int) <=>
    !k:int.
      (&0:int) <= k /\ k < upper
      ==> ntp4vc_sc_nth a k = ntp4vc_sc_elts m k j`;;

let ntp4vc_sc_other_columns = new_definition
 `ntp4vc_sc_other_columns
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int))
    (j:int) <=>
    !k l:int.
      (((&0:int) <= k /\ k < ntp4vc_sc_rows current) /\
       ((&0:int) <= l /\ l < ntp4vc_sc_columns current) /\
       ~(l = j))
      ==> ntp4vc_sc_elts current k l =
          ntp4vc_sc_elts original k l`;;

let ntp4vc_sc_column_sorted = new_definition
 `ntp4vc_sc_column_sorted
    (m:(int#int)#(int->int->int)) (j:int) <=>
    !i k:int.
      (&0:int) <= i /\ i <= k /\ k < ntp4vc_sc_rows m
      ==> ntp4vc_sc_elts m i j <= ntp4vc_sc_elts m k j`;;

let ntp4vc_sc_column_permuted = new_definition
 `ntp4vc_sc_column_permuted
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int))
    (j:int) <=>
    ntp4vc_sc_permut
      (ntp4vc_sc_column current j)
      (ntp4vc_sc_column original j)
      (&0:int)
      (ntp4vc_sc_rows current)`;;

let ntp4vc_sc_post = new_definition
 `ntp4vc_sc_post
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int))
    (j:int) <=>
    ntp4vc_sc_other_columns current original j /\
    ntp4vc_sc_column_sorted current j /\
    ntp4vc_sc_column_permuted current original j`;;

let ntp4vc_sc_array_sorted = new_definition
 `ntp4vc_sc_array_sorted (a:int list) <=>
    !i k:int.
      (&0:int) <= i /\ i <= k /\ k < (&(LENGTH a):int)
      ==> ntp4vc_sc_nth a i <= ntp4vc_sc_nth a k`;;

let ntp4vc_sc_array_permuted = new_definition
 `ntp4vc_sc_array_permuted (current:int list) (previous:int list) <=>
    ntp4vc_sc_permut
      (ntp4vc_sc_nth current)
      (ntp4vc_sc_nth previous)
      (&0:int)
      (&(LENGTH current):int)`;;

let ntp4vc_sc_matrix_update = new_definition
 `ntp4vc_sc_matrix_update
    (m:(int#int)#(int->int->int))
    (i:int) (j:int) (value:int) =
    \r c.
      if r = i
      then if c = j then value else ntp4vc_sc_elts m r c
      else ntp4vc_sc_elts m r c`;;

let ntp4vc_sc_write_iteration = new_definition
 `ntp4vc_sc_write_iteration
    (a:int list)
    (original:(int#int)#(int->int->int))
    (j:int)
    (upper:int)
    (current:(int#int)#(int->int->int)) <=>
    (!i:int.
       (((&0:int) <= i /\ i <= upper) /\
        ntp4vc_sc_prefix a current j i /\
        ntp4vc_sc_other_columns current original j)
       ==>
       ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
       ntp4vc_sc_valid_index current i j /\
       (!next:(int#int)#(int->int->int).
          ntp4vc_sc_matrix next /\
          ntp4vc_sc_same_dimensions next current
          ==>
          ntp4vc_sc_elts next =
            ntp4vc_sc_matrix_update
              current i j (ntp4vc_sc_nth a i)
          ==>
          ntp4vc_sc_prefix a next j (i + (&1:int)) /\
          ntp4vc_sc_other_columns next original j)) /\
    ((ntp4vc_sc_prefix a current j (upper + (&1:int)) /\
      ntp4vc_sc_other_columns current original j)
     ==> ntp4vc_sc_post current original j)`;;

let ntp4vc_sc_write_loop = new_definition
 `ntp4vc_sc_write_loop
    (a:int list)
    (original:(int#int)#(int->int->int))
    (j:int) <=>
    let upper = ntp4vc_sc_rows original - (&1:int) in
    (((&0:int) <= upper + (&1:int)
      ==>
      ntp4vc_sc_prefix a original j (&0:int) /\
      (!current:(int#int)#(int->int->int).
         ntp4vc_sc_matrix current /\
         ntp4vc_sc_same_dimensions current original
         ==>
         ntp4vc_sc_write_iteration a original j upper current)) /\
     (upper + (&1:int) < (&0:int)
      ==> ntp4vc_sc_post original original j))`;;

let ntp4vc_sc_read_iteration = new_definition
 `ntp4vc_sc_read_iteration
    (a:int list)
    (original:(int#int)#(int->int->int))
    (j:int)
    (upper:int)
    (current:int list) <=>
    (!i:int.
       (((&0:int) <= i /\ i <= upper) /\
        ntp4vc_sc_prefix current original j i)
       ==>
       ntp4vc_sc_valid_index original i j /\
       (let value = ntp4vc_sc_elts original i j in
        ((&0:int) <= i /\ i < (&(LENGTH current):int)) /\
        (LENGTH
           (ntp4vc_sc_update current (ntp4vc_sc_to_num i) value) =
         LENGTH current
         ==>
         (\r:int.
            ntp4vc_sc_nth
              (ntp4vc_sc_update current (ntp4vc_sc_to_num i) value)
              r) =
           (\r:int.
              if r = i then value else ntp4vc_sc_nth current r)
         ==>
         ntp4vc_sc_prefix
           (ntp4vc_sc_update current (ntp4vc_sc_to_num i) value)
           original j (i + (&1:int))))) /\
    (ntp4vc_sc_prefix current original j (upper + (&1:int))
     ==>
     (!sorted:int list.
        LENGTH sorted = LENGTH current
        ==>
        ntp4vc_sc_array_sorted sorted /\
        ntp4vc_sc_array_permuted sorted current
        ==>
        ntp4vc_sc_write_loop sorted original j))`;;

let ntp4vc_sc_read_loop = new_definition
 `ntp4vc_sc_read_loop
    (a:int list)
    (original:(int#int)#(int->int->int))
    (j:int) <=>
    let upper = ntp4vc_sc_rows original - (&1:int) in
    (((&0:int) <= upper + (&1:int)
      ==>
      ntp4vc_sc_prefix a original j (&0:int) /\
      (!current:int list.
         LENGTH current = LENGTH a
         ==>
         ntp4vc_sc_read_iteration a original j upper current)) /\
     (upper + (&1:int) < (&0:int)
      ==>
      (!sorted:int list.
         LENGTH sorted = LENGTH a
         ==>
         ntp4vc_sc_array_sorted sorted /\
         ntp4vc_sc_array_permuted sorted a
         ==>
         ntp4vc_sc_write_loop sorted original j)))`;;

let statement =
 `!j:int. !m:(int#int)#(int->int->int).
    ntp4vc_sc_matrix m
    ==>
    (&0:int) <= j
    ==>
    j < ntp4vc_sc_columns m
    ==>
    let rows = ntp4vc_sc_rows m in
    (&0:int) <= rows /\
    (!a:int list.
       ((!i:int.
           (&0:int) <= i /\ i < rows
           ==> ntp4vc_sc_nth a i = (&0:int)) /\
        (&(LENGTH a):int) = rows)
       ==>
       ntp4vc_sc_read_loop a m j)`;;
