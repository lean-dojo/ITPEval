(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_sparse_array_SparseArray_setqtvc: the sparse-array set
  verification condition, preserving representation invariants through value,
  index, back-pointer, and cardinality updates and the final point-update
  specification. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  vacid_set_sparse_array =
    VacidSetSparseArray ('a list) (int list) (int list) int 'a
End

val vacid_set_values_def = Define `
  vacid_set_values
      (VacidSetSparseArray values index back card default) = values`;

val vacid_set_index_def = Define `
  vacid_set_index
      (VacidSetSparseArray values index back card default) = index`;

val vacid_set_back_def = Define `
  vacid_set_back
      (VacidSetSparseArray values index back card default) = back`;

val vacid_set_card_def = Define `
  vacid_set_card
      (VacidSetSparseArray values index back card default) = card`;

val vacid_set_default_def = Define `
  vacid_set_default
      (VacidSetSparseArray values index back card default) = default`;

val vacid_set_to_num_def = Define `
  vacid_set_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val vacid_set_nth_def = Define `
  vacid_set_nth (xs : 'a list) (i : int) =
    if i < (0 : int) then
      ARB
    else if vacid_set_to_num i < LENGTH xs then
      EL (vacid_set_to_num i) xs
    else
      ARB`;

val vacid_set_fun_update_def = Define `
  vacid_set_fun_update (f : 'a -> 'b) (key : 'a) (value : 'b) =
    \q. if q = key then value else f q`;

val vacid_set_rep_ok_def = Define `
  vacid_set_rep_ok
      (values : 'a list)
      (index : int list)
      (back : int list)
      (card : int) <=>
    (0 : int) <= card /\
    card <= &(LENGTH values) /\
    &(LENGTH values) <= (1000 : int) /\
    LENGTH values = LENGTH index /\
    LENGTH index = LENGTH back /\
    !j : int.
      (0 : int) <= j /\ j < card ==>
      (0 : int) <= vacid_set_nth back j /\
      vacid_set_nth back j < &(LENGTH values) /\
      vacid_set_nth index (vacid_set_nth back j) = j`;

val vacid_set_valid_def = Define `
  vacid_set_valid (a : 'a vacid_set_sparse_array) <=>
    vacid_set_rep_ok
      (vacid_set_values a)
      (vacid_set_index a)
      (vacid_set_back a)
      (vacid_set_card a)`;

val vacid_set_is_elt_def = Define `
  vacid_set_is_elt (a : 'a vacid_set_sparse_array) (i : int) <=>
    ((0 : int) <= vacid_set_nth (vacid_set_index a) i /\
     vacid_set_nth (vacid_set_index a) i < vacid_set_card a) /\
    vacid_set_nth
      (vacid_set_back a)
      (vacid_set_nth (vacid_set_index a) i) = i`;

val vacid_set_value_def = Define `
  vacid_set_value (a : 'a vacid_set_sparse_array) (i : int) =
    if vacid_set_is_elt a i then
      vacid_set_nth (vacid_set_values a) i
    else
      vacid_set_default a`;

val vacid_set_length_def = Define `
  vacid_set_length (a : 'a vacid_set_sparse_array) =
    &(LENGTH (vacid_set_values a))`;

val vacid_0_sparse_array_SparseArray_setqtvc_statement =
  ``!(a : 'a vacid_set_sparse_array) (i : int) (v : 'a).
      vacid_set_valid a /\
      (0 : int) <= i /\
      i < vacid_set_length a
      ==>
      let o1 = vacid_set_values a
      in
        ((0 : int) <= i /\ i < &(LENGTH o1)) /\
        !a1 : 'a vacid_set_sparse_array.
          vacid_set_valid a1 ==>
          LENGTH (LUPDATE v (vacid_set_to_num i) o1) = LENGTH o1 ==>
          LENGTH (LUPDATE v (vacid_set_to_num i) o1) =
            LENGTH (vacid_set_values a) ==>
          vacid_set_nth (LUPDATE v (vacid_set_to_num i) o1) =
            vacid_set_fun_update (vacid_set_nth o1) i v ==>
          vacid_set_rep_ok
            (LUPDATE v (vacid_set_to_num i) o1)
            (vacid_set_index a)
            (vacid_set_back a)
            (vacid_set_card a) /\
          (vacid_set_default a = vacid_set_default a1 /\
           vacid_set_card a = vacid_set_card a1 /\
           vacid_set_back a = vacid_set_back a1 /\
           vacid_set_index a = vacid_set_index a1 /\
           LUPDATE v (vacid_set_to_num i) o1 =
             vacid_set_values a1
           ==>
           ((0 : int) <= i /\ i < vacid_set_length a1) /\
           if ~vacid_set_is_elt a1 i then
             let o2 = vacid_set_card a1
             in
             let o3 = vacid_set_index a1
             in
               ((0 : int) <= i /\ i < &(LENGTH o3)) /\
               (LENGTH (LUPDATE o2 (vacid_set_to_num i) o3) =
                  LENGTH o3 ==>
                LENGTH (LUPDATE o2 (vacid_set_to_num i) o3) =
                  LENGTH (vacid_set_index a1) ==>
                vacid_set_nth
                    (LUPDATE o2 (vacid_set_to_num i) o3) =
                  vacid_set_fun_update (vacid_set_nth o3) i o2 ==>
                ((0 : int) <= vacid_set_card a1 /\
                 vacid_set_card a1 <
                   &(LENGTH (vacid_set_back a1))) /\
                (LENGTH
                    (LUPDATE
                      i
                      (vacid_set_to_num (vacid_set_card a1))
                      (vacid_set_back a1)) =
                   LENGTH (vacid_set_back a1) ==>
                 LENGTH
                    (LUPDATE
                      i
                      (vacid_set_to_num (vacid_set_card a1))
                      (vacid_set_back a1)) =
                   LENGTH (vacid_set_back a1) ==>
                 vacid_set_nth
                     (LUPDATE
                       i
                       (vacid_set_to_num (vacid_set_card a1))
                       (vacid_set_back a1)) =
                   vacid_set_fun_update
                     (vacid_set_nth (vacid_set_back a1))
                     (vacid_set_card a1)
                     i ==>
                 !a2 : 'a vacid_set_sparse_array.
                   vacid_set_valid a2 ==>
                   vacid_set_rep_ok
                     (vacid_set_values a1)
                     (LUPDATE o2 (vacid_set_to_num i) o3)
                     (LUPDATE
                       i
                       (vacid_set_to_num (vacid_set_card a1))
                       (vacid_set_back a1))
                     (vacid_set_card a1 + (1 : int)) /\
                   (vacid_set_default a1 = vacid_set_default a2 /\
                    vacid_set_card a1 + (1 : int) =
                      vacid_set_card a2 /\
                    LUPDATE
                        i
                        (vacid_set_to_num (vacid_set_card a1))
                        (vacid_set_back a1) =
                      vacid_set_back a2 /\
                    LUPDATE o2 (vacid_set_to_num i) o3 =
                      vacid_set_index a2 /\
                    vacid_set_values a1 = vacid_set_values a2
                    ==>
                    vacid_set_value a2 i = v /\
                    !j : int.
                      ~(j = i) ==>
                      vacid_set_value a2 j =
                        vacid_set_value a j)))
           else
             vacid_set_value a1 i = v /\
             !j : int.
               ~(j = i) ==>
               vacid_set_value a1 j = vacid_set_value a j)``;
