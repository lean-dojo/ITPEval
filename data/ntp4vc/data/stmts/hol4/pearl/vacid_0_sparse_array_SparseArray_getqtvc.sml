(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_sparse_array_SparseArray_getqtvc: the sparse-array get
  verification condition, preserving index bounds and agreement between the
  conditional returned value and the abstract sparse-array value. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  vacid_get_sparse_array =
    VacidGetSparseArray ('a list) (int list) (int list) int 'a
End

val vacid_get_values_def = Define `
  vacid_get_values
      (VacidGetSparseArray values index back card default) = values`;

val vacid_get_index_def = Define `
  vacid_get_index
      (VacidGetSparseArray values index back card default) = index`;

val vacid_get_back_def = Define `
  vacid_get_back
      (VacidGetSparseArray values index back card default) = back`;

val vacid_get_card_def = Define `
  vacid_get_card
      (VacidGetSparseArray values index back card default) = card`;

val vacid_get_default_def = Define `
  vacid_get_default
      (VacidGetSparseArray values index back card default) = default`;

val vacid_get_to_num_def = Define `
  vacid_get_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val vacid_get_nth_def = Define `
  vacid_get_nth (xs : 'a list) (i : int) =
    if vacid_get_to_num i < LENGTH xs then
      EL (vacid_get_to_num i) xs
    else
      ARB`;

val vacid_get_valid_def = Define `
  vacid_get_valid (a : 'a vacid_get_sparse_array) <=>
    (0 : int) <= vacid_get_card a /\
    vacid_get_card a <= &(LENGTH (vacid_get_values a)) /\
    &(LENGTH (vacid_get_values a)) <= (1000 : int) /\
    LENGTH (vacid_get_values a) = LENGTH (vacid_get_index a) /\
    LENGTH (vacid_get_index a) = LENGTH (vacid_get_back a) /\
    !j : int.
      (0 : int) <= j /\ j < vacid_get_card a ==>
      (0 : int) <= vacid_get_nth (vacid_get_back a) j /\
      vacid_get_nth (vacid_get_back a) j <
        &(LENGTH (vacid_get_values a)) /\
      vacid_get_nth
        (vacid_get_index a)
        (vacid_get_nth (vacid_get_back a) j) = j`;

val vacid_get_is_elt_def = Define `
  vacid_get_is_elt (a : 'a vacid_get_sparse_array) (i : int) <=>
    ((0 : int) <= vacid_get_nth (vacid_get_index a) i /\
     vacid_get_nth (vacid_get_index a) i < vacid_get_card a) /\
    vacid_get_nth
      (vacid_get_back a)
      (vacid_get_nth (vacid_get_index a) i) = i`;

val vacid_get_value_def = Define `
  vacid_get_value (a : 'a vacid_get_sparse_array) (i : int) =
    if vacid_get_is_elt a i then
      vacid_get_nth (vacid_get_values a) i
    else
      vacid_get_default a`;

val vacid_get_length_def = Define `
  vacid_get_length (a : 'a vacid_get_sparse_array) =
    &(LENGTH (vacid_get_values a))`;

val vacid_0_sparse_array_SparseArray_getqtvc_statement =
  ``!(a : 'a vacid_get_sparse_array) (i : int).
      vacid_get_valid a /\
      (0 : int) <= i /\
      i < vacid_get_length a
      ==>
      (0 : int) <= i /\
      i < vacid_get_length a /\
      (vacid_get_is_elt a i ==>
       (0 : int) <= i /\
       i < &(LENGTH (vacid_get_values a))) /\
      !result : 'a.
        (if vacid_get_is_elt a i then
           result = vacid_get_nth (vacid_get_values a) i
         else
           result = vacid_get_default a)
        ==>
        result = vacid_get_value a i``;
