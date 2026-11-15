(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_sort_rowqtvc: the full
  verification condition for copying, sorting, optionally reversing, and
  writing back one row of an integer matrix while preserving all other rows
  and the selected row's multiset. This file contains no proof.
*)

let ntp4vc_sr_rows = new_definition
 `ntp4vc_sr_rows
    (m:(int#int)#(int->int->int)) = FST (FST m)`;;

let ntp4vc_sr_columns = new_definition
 `ntp4vc_sr_columns
    (m:(int#int)#(int->int->int)) = SND (FST m)`;;

let ntp4vc_sr_elts = new_definition
 `ntp4vc_sr_elts
    (m:(int#int)#(int->int->int)) (i:int) (j:int) = SND m i j`;;

let ntp4vc_sr_matrix = new_definition
 `ntp4vc_sr_matrix (m:(int#int)#(int->int->int)) <=>
    (&0:int) <= ntp4vc_sr_rows m /\
    (&0:int) <= ntp4vc_sr_columns m`;;

let ntp4vc_sr_same_dimensions = new_definition
 `ntp4vc_sr_same_dimensions
    (m1:(int#int)#(int->int->int))
    (m2:(int#int)#(int->int->int)) <=>
    ntp4vc_sr_rows m1 = ntp4vc_sr_rows m2 /\
    ntp4vc_sr_columns m1 = ntp4vc_sr_columns m2`;;

let ntp4vc_sr_valid_index = new_definition
 `ntp4vc_sr_valid_index
    (m:(int#int)#(int->int->int)) (i:int) (j:int) <=>
    ((&0:int) <= i /\ i < ntp4vc_sr_rows m) /\
    (&0:int) <= j /\ j < ntp4vc_sr_columns m`;;

let ntp4vc_sr_to_num = new_definition
 `ntp4vc_sr_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sr_nth = new_definition
 `ntp4vc_sr_nth (a:int list) (i:int) =
    if ntp4vc_sr_to_num i < LENGTH a
    then EL (ntp4vc_sr_to_num i) a
    else (&0:int)`;;

let ntp4vc_sr_update =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:int.
       ntp4vc_sr_update ([]:int list) n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       ntp4vc_sr_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (ntp4vc_sr_update t (PRE n) x))`;;

let ntp4vc_sr_permut = new_definition
 `ntp4vc_sr_permut
    (first:int->int) (second:int->int) (lower:int) (upper:int) <=>
    !value:int.
      CARD {index:int |
              lower <= index /\ index < upper /\ first index = value} =
      CARD {index:int |
              lower <= index /\ index < upper /\ second index = value}`;;

let ntp4vc_sr_prefix = new_definition
 `ntp4vc_sr_prefix
    (a:int list)
    (m:(int#int)#(int->int->int))
    (i:int) (upper:int) <=>
    !k:int.
      (&0:int) <= k /\ k < upper
      ==> ntp4vc_sr_nth a k = ntp4vc_sr_elts m i k`;;

let ntp4vc_sr_other_rows = new_definition
 `ntp4vc_sr_other_rows
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int))
    (i:int) <=>
    !k l:int.
      (((&0:int) <= k /\ k < ntp4vc_sr_rows current) /\
       ((&0:int) <= l /\ l < ntp4vc_sr_columns current) /\
       ~(k = i))
      ==> ntp4vc_sr_elts current k l =
          ntp4vc_sr_elts original k l`;;

let ntp4vc_sr_row_sorted = new_definition
 `ntp4vc_sr_row_sorted
    (m:(int#int)#(int->int->int)) (i:int) (ascending:bool) <=>
    !j k:int.
      (&0:int) <= j /\ j <= k /\ k < ntp4vc_sr_columns m
      ==> if ascending
          then ntp4vc_sr_elts m i j <= ntp4vc_sr_elts m i k
          else ntp4vc_sr_elts m i k <= ntp4vc_sr_elts m i j`;;

let ntp4vc_sr_row_permuted = new_definition
 `ntp4vc_sr_row_permuted
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int))
    (i:int) <=>
    ntp4vc_sr_permut
      (ntp4vc_sr_elts current i)
      (ntp4vc_sr_elts original i)
      (&0:int)
      (ntp4vc_sr_columns current)`;;

let ntp4vc_sr_post = new_definition
 `ntp4vc_sr_post
    (current:(int#int)#(int->int->int))
    (original:(int#int)#(int->int->int))
    (i:int) (ascending:bool) <=>
    ntp4vc_sr_other_rows current original i /\
    ntp4vc_sr_row_sorted current i ascending /\
    ntp4vc_sr_row_permuted current original i`;;

let ntp4vc_sr_array_sorted = new_definition
 `ntp4vc_sr_array_sorted (a:int list) <=>
    !i j:int.
      (&0:int) <= i /\ i <= j /\ j < (&(LENGTH a):int)
      ==> ntp4vc_sr_nth a i <= ntp4vc_sr_nth a j`;;

let ntp4vc_sr_array_permuted = new_definition
 `ntp4vc_sr_array_permuted (current:int list) (previous:int list) <=>
    ntp4vc_sr_permut
      (ntp4vc_sr_nth current)
      (ntp4vc_sr_nth previous)
      (&0:int)
      (&(LENGTH current):int)`;;

let ntp4vc_sr_matrix_update = new_definition
 `ntp4vc_sr_matrix_update
    (m:(int#int)#(int->int->int))
    (i:int) (j:int) (value:int) =
    \r c.
      if r = i
      then if c = j then value else ntp4vc_sr_elts m r c
      else ntp4vc_sr_elts m r c`;;

let ntp4vc_sr_write_iteration = new_definition
 `ntp4vc_sr_write_iteration
    (a:int list)
    (original:(int#int)#(int->int->int))
    (i:int)
    (ascending:bool)
    (upper:int)
    (current:(int#int)#(int->int->int)) <=>
    (!j:int.
       (((&0:int) <= j /\ j <= upper) /\
        ntp4vc_sr_prefix a current i j /\
        ntp4vc_sr_other_rows current original i)
       ==>
       ((&0:int) <= j /\ j < (&(LENGTH a):int)) /\
       ntp4vc_sr_valid_index current i j /\
       (!next:(int#int)#(int->int->int).
          ntp4vc_sr_matrix next /\
          ntp4vc_sr_same_dimensions next current
          ==>
          ntp4vc_sr_elts next =
            ntp4vc_sr_matrix_update
              current i j (ntp4vc_sr_nth a j)
          ==>
          ntp4vc_sr_prefix a next i (j + (&1:int)) /\
          ntp4vc_sr_other_rows next original i)) /\
    ((ntp4vc_sr_prefix a current i (upper + (&1:int)) /\
      ntp4vc_sr_other_rows current original i)
     ==> ntp4vc_sr_post current original i ascending)`;;

let ntp4vc_sr_write_loop = new_definition
 `ntp4vc_sr_write_loop
    (a:int list)
    (original:(int#int)#(int->int->int))
    (i:int)
    (ascending:bool) <=>
    let upper = ntp4vc_sr_columns original - (&1:int) in
    (((&0:int) <= upper + (&1:int)
      ==>
      ntp4vc_sr_prefix a original i (&0:int) /\
      (!current:(int#int)#(int->int->int).
         ntp4vc_sr_matrix current /\
         ntp4vc_sr_same_dimensions current original
         ==>
         ntp4vc_sr_write_iteration
           a original i ascending upper current)) /\
     (upper + (&1:int) < (&0:int)
      ==> ntp4vc_sr_post original original i ascending))`;;

let ntp4vc_sr_reverse_initial = new_definition
 `ntp4vc_sr_reverse_initial (base:int list) <=>
    let upper = (&(LENGTH base):int) - (&1:int) in
    (((&0:int) <= (&0:int) /\
      (&0:int) <= upper + (&1:int) /\
      upper + (&1:int) <= (&(LENGTH base):int)) /\
     (&0:int) + upper = (&(LENGTH base):int) - (&1:int) /\
     (!j:int.
        ((&0:int) <= j /\ j < (&0:int)) \/
        (upper < j /\ j < (&(LENGTH base):int))
        ==> ntp4vc_sr_nth base j =
            ntp4vc_sr_nth base ((&(LENGTH base):int) - (&1:int) - j)) /\
     ntp4vc_sr_permut
       (ntp4vc_sr_nth base)
       (ntp4vc_sr_nth base)
       (&0:int)
       (&(LENGTH base):int))`;;

let ntp4vc_sr_reverse_invariant = new_definition
 `ntp4vc_sr_reverse_invariant
    (base:int list) (current:int list) (u:int) (v:int) <=>
    ((&0:int) <= u /\
     u <= v + (&1:int) /\
     v + (&1:int) <= (&(LENGTH current):int)) /\
    u + v = (&(LENGTH current):int) - (&1:int) /\
    (!j:int.
       u <= j /\ j <= v
       ==> ntp4vc_sr_nth current j = ntp4vc_sr_nth base j) /\
    (!j:int.
       ((&0:int) <= j /\ j < u) \/
       (v < j /\ j < (&(LENGTH current):int))
       ==> ntp4vc_sr_nth current j =
           ntp4vc_sr_nth base
             ((&(LENGTH current):int) - (&1:int) - j)) /\
    ntp4vc_sr_permut
      (ntp4vc_sr_nth base)
      (ntp4vc_sr_nth current)
      (&0:int)
      (&(LENGTH current):int)`;;

let ntp4vc_sr_swap_effect = new_definition
 `ntp4vc_sr_swap_effect
    (before:int list) (after:int list) (u:int) (v:int) <=>
    let size = (&(LENGTH after):int) in
    ((((&0:int) <= u /\ u < size) /\
      (&0:int) <= v /\ v < size) /\
     (!index:int.
        (((&0:int) <= index /\ index <= size) /\
         ~(index = u) /\ ~(index = v))
        ==> ntp4vc_sr_nth after index =
            ntp4vc_sr_nth before index) /\
     ntp4vc_sr_nth after u = ntp4vc_sr_nth before v /\
     ntp4vc_sr_nth after v = ntp4vc_sr_nth before u)`;;

let ntp4vc_sr_reverse_step_post = new_definition
 `ntp4vc_sr_reverse_step_post
    (base:int list) (current:int list) (u:int) (v:int) <=>
    ((&0:int) <= v - u /\
     v - (&1:int) - (u + (&1:int)) < v - u) /\
    ntp4vc_sr_reverse_invariant
      base current (u + (&1:int)) (v - (&1:int))`;;

let ntp4vc_sr_swap_case = new_definition
 `ntp4vc_sr_swap_case
    (base:int list) (current:int list) (u:int) (v:int) <=>
    ((&0:int) <= v /\ v < (&(LENGTH current):int)) /\
    (let tmp = ntp4vc_sr_nth current v in
     ((&0:int) <= u /\ u < (&(LENGTH current):int)) /\
     (let old_u = ntp4vc_sr_nth current u in
      ((&0:int) <= v /\ v < (&(LENGTH current):int)) /\
      (let at_v =
         ntp4vc_sr_update current (ntp4vc_sr_to_num v) old_u in
       (LENGTH at_v = LENGTH current
        ==>
        ((\index:int. ntp4vc_sr_nth at_v index) =
           (\index:int.
              if index = v then old_u
              else ntp4vc_sr_nth current index)
         ==>
         (((&0:int) <= u /\ u < (&(LENGTH at_v):int)) /\
          (let swapped =
             ntp4vc_sr_update at_v (ntp4vc_sr_to_num u) tmp in
           (LENGTH swapped = LENGTH at_v
            ==>
            ((\index:int. ntp4vc_sr_nth swapped index) =
               (\index:int.
                  if index = u then tmp
                  else ntp4vc_sr_nth at_v index)
             ==>
             (ntp4vc_sr_swap_effect current swapped u v /\
              (ntp4vc_sr_permut
                 (ntp4vc_sr_nth swapped)
                 (ntp4vc_sr_nth current)
                 (&0:int)
                 (&(LENGTH swapped):int)
               ==>
               ntp4vc_sr_reverse_step_post
                 base swapped u v)))))))))))`;;

let ntp4vc_sr_reverse_loop = new_definition
 `ntp4vc_sr_reverse_loop
    (base:int list)
    (original:(int#int)#(int->int->int))
    (i:int)
    (ascending:bool) <=>
    ntp4vc_sr_reverse_initial base /\
    (!v u:int. !current:int list.
       LENGTH current = LENGTH base
       ==>
       ntp4vc_sr_reverse_invariant base current u v
       ==>
       if u < v
       then ntp4vc_sr_swap_case base current u v
       else ntp4vc_sr_write_loop current original i ascending)`;;

let ntp4vc_sr_after_sort = new_definition
 `ntp4vc_sr_after_sort
    (sorted:int list)
    (original:(int#int)#(int->int->int))
    (i:int)
    (ascending:bool) <=>
    if ~ascending
    then ntp4vc_sr_reverse_loop sorted original i ascending
    else ntp4vc_sr_write_loop sorted original i ascending`;;

let ntp4vc_sr_read_iteration = new_definition
 `ntp4vc_sr_read_iteration
    (a:int list)
    (original:(int#int)#(int->int->int))
    (i:int)
    (ascending:bool)
    (upper:int)
    (current:int list) <=>
    (!j:int.
       (((&0:int) <= j /\ j <= upper) /\
        ntp4vc_sr_prefix current original i j)
       ==>
       ntp4vc_sr_valid_index original i j /\
       (let value = ntp4vc_sr_elts original i j in
        ((&0:int) <= j /\ j < (&(LENGTH current):int)) /\
        (LENGTH
           (ntp4vc_sr_update current (ntp4vc_sr_to_num j) value) =
         LENGTH current
         ==>
         (\index:int.
            ntp4vc_sr_nth
              (ntp4vc_sr_update current (ntp4vc_sr_to_num j) value)
              index) =
           (\index:int.
              if index = j then value
              else ntp4vc_sr_nth current index)
         ==>
         ntp4vc_sr_prefix
           (ntp4vc_sr_update current (ntp4vc_sr_to_num j) value)
           original i (j + (&1:int))))) /\
    (ntp4vc_sr_prefix current original i (upper + (&1:int))
     ==>
     (!sorted:int list.
        LENGTH sorted = LENGTH current
        ==>
        ntp4vc_sr_array_sorted sorted /\
        ntp4vc_sr_array_permuted sorted current
        ==>
        ntp4vc_sr_after_sort sorted original i ascending))`;;

let ntp4vc_sr_read_loop = new_definition
 `ntp4vc_sr_read_loop
    (a:int list)
    (original:(int#int)#(int->int->int))
    (i:int)
    (ascending:bool) <=>
    let upper = ntp4vc_sr_columns original - (&1:int) in
    (((&0:int) <= upper + (&1:int)
      ==>
      ntp4vc_sr_prefix a original i (&0:int) /\
      (!current:int list.
         LENGTH current = LENGTH a
         ==>
         ntp4vc_sr_read_iteration
           a original i ascending upper current)) /\
     (upper + (&1:int) < (&0:int)
      ==>
      (!sorted:int list.
         LENGTH sorted = LENGTH a
         ==>
         ntp4vc_sr_array_sorted sorted /\
         ntp4vc_sr_array_permuted sorted a
         ==>
         ntp4vc_sr_after_sort sorted original i ascending)))`;;

let statement =
 `!i:int. !m:(int#int)#(int->int->int). !ascending:bool.
    ntp4vc_sr_matrix m
    ==>
    (&0:int) <= i
    ==>
    i < ntp4vc_sr_rows m
    ==>
    let columns = ntp4vc_sr_columns m in
    (&0:int) <= columns /\
    (!a:int list.
       ((!j:int.
           (&0:int) <= j /\ j < columns
           ==> ntp4vc_sr_nth a j = (&0:int)) /\
        (&(LENGTH a):int) = columns)
       ==>
       ntp4vc_sr_read_loop a m i ascending)`;;
