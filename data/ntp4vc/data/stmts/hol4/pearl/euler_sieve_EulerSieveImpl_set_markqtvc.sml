(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/euler_sieve_EulerSieveImpl_set_markqtvc: the verification condition
  for marking an odd Euler-sieve index, updating its compact successor array,
  and preserving the sieve state invariant. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val esm_to_num_def = Define `
  esm_to_num (z : int) = if z < 0 then 0 else Num z`;

val esm_get_int_def = Define `
  esm_get_int (xs : int list) (i : int) =
    if esm_to_num i < LENGTH xs then EL (esm_to_num i) xs else (0 : int)`;

val esm_get_bool_def = Define `
  esm_get_bool (xs : bool list) (i : int) =
    if esm_to_num i < LENGTH xs then EL (esm_to_num i) xs else F`;

val esm_update_def = Define `
  esm_update (xs : 'a list) (i : int) (x : 'a) =
    LUPDATE x (esm_to_num i) xs`;

val esm_in_bounds_def = Define `
  esm_in_bounds (z : int) <=>
    (-4611686018427387904 : int) <= z /\
    z <= (4611686018427387903 : int)`;

val esm_array_invariant_def = Define `
  esm_array_invariant
    (elts : 'array -> int list)
    (size : 'array -> int)
    (self : 'array) <=>
      (0 : int) <= size self /\
      size self = &(LENGTH (elts self)) /\
      &(LENGTH (elts self)) <= (4611686018427387903 : int) /\
      !i : int.
        (0 : int) <= i /\ i < &(LENGTH (elts self)) ==>
        esm_in_bounds (esm_get_int (elts self) i)`;

val esm_inv_nexts_def = Define `
  esm_inv_nexts (nexts : int list) (n : int) <=>
    !i : int.
      (0 : int) <= i /\ i < n ==>
      i < esm_get_int nexts i /\ esm_get_int nexts i <= n`;

val esm_all_eliminated_def = Define `
  esm_all_eliminated (marked : bool list) (nexts : int list) <=>
    LENGTH marked = LENGTH nexts /\
    !i : int.
      (0 : int) <= i /\ i < &(LENGTH marked) ==>
      !j : int.
        i < j /\ j < esm_get_int nexts i ==>
        esm_get_bool marked j = T`;

val esm_state_invariant_def = Define `
  esm_state_invariant
    (elts : 'array -> int list)
    (nexts : int list)
    (marked : bool list)
    (arr : 'array)
    (maximum : int)
    (maximum_arr : int) <=>
      maximum < (4611686018427387903 : int) /\
      (3 : int) <= maximum /\
      LENGTH nexts = LENGTH marked /\
      &(LENGTH marked) = maximum + (1 : int) /\
      (maximum - (1 : int)) quot (2 : int) = maximum_arr /\
      &(LENGTH (elts arr)) = maximum_arr + (1 : int) /\
      esm_inv_nexts nexts (&(LENGTH nexts)) /\
      esm_all_eliminated marked nexts /\
      (!i : int.
         (3 : int) <= i /\ i <= maximum ==>
         i rem (2 : int) = (0 : int) ==>
         esm_get_bool marked i = T) /\
      (!i : int.
         (3 : int) <= i /\ i < maximum - (1 : int) ==>
         i rem (2 : int) = (1 : int) ==>
         esm_get_int nexts i rem (2 : int) = (1 : int) \/
         esm_get_int nexts i = maximum + (1 : int)) /\
      esm_get_int nexts maximum = maximum + (1 : int) /\
      ((maximum - (1 : int)) rem (2 : int) = (0 : int) ==>
       esm_get_int nexts (maximum - (1 : int)) = maximum) /\
      ((maximum - (1 : int)) rem (2 : int) = (1 : int) ==>
       esm_get_int nexts (maximum - (1 : int)) =
         maximum + (1 : int)) /\
      (!i : int.
         (0 : int) <= i /\ i <= maximum_arr ==>
         -(maximum + (1 : int)) <= esm_get_int (elts arr) i /\
         esm_get_int (elts arr) i <= maximum + (1 : int)) /\
      (!i : int.
         (0 : int) <= i /\ i <= maximum_arr ==>
         (esm_get_bool marked ((2 : int) * i + (1 : int)) = T <=>
          esm_get_int (elts arr) i < (0 : int))) /\
      (!i : int.
         (0 : int) <= i /\ i <= maximum_arr ==>
         ~(esm_get_bool marked ((2 : int) * i + (1 : int)) = T) ==>
         esm_get_int (elts arr) i =
           esm_get_int nexts ((2 : int) * i + (1 : int))) /\
      (!i : int.
         (0 : int) <= i /\ i <= maximum_arr ==>
         esm_get_bool marked ((2 : int) * i + (1 : int)) = T ==>
         esm_get_int (elts arr) i =
           -esm_get_int nexts ((2 : int) * i + (1 : int))) /\
      (!i : int.
         (0 : int) <= i /\ i <= maximum_arr ==>
         (i < ABS (esm_get_int (elts arr) i) quot (2 : int) /\
          ABS (esm_get_int (elts arr) i) quot (2 : int) <=
            maximum_arr + (1 : int)) /\
         ABS (esm_get_int (elts arr) i) <= maximum + (1 : int)) /\
      !i j : int.
        (0 : int) <= i /\ i <= maximum_arr ==>
        i < j /\ j < ABS (esm_get_int (elts arr) i) quot (2 : int) ==>
        esm_get_int (elts arr) j < (0 : int)`;

val esm_result_condition_def = Define `
  esm_result_condition
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (arr : 'state -> 'array)
    (max_of : 'state -> 63 word)
    (max_arr_of : 'state -> 63 word)
    (elts : 'array -> int list)
    (t1 : 'state)
    (marked1 : bool list)
    (arr1 : 'array)
    (index : int) <=>
      !t2 : 'state.
        esm_state_invariant elts (nexts t1) marked1 arr1
          (w2i (max_of t1)) (w2i (max_arr_of t1)) /\
        (max_arr_of t1 = max_arr_of t2 /\
         max_of t1 = max_of t2 /\
         arr1 = arr t2 /\
         marked1 = marked t2 /\
         nexts t1 = nexts t2 ==>
         marked t2 = esm_update (marked t1) index T)`;

val esm_marking_condition_def = Define `
  esm_marking_condition
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (arr : 'state -> 'array)
    (max_of : 'state -> 63 word)
    (max_arr_of : 'state -> 63 word)
    (elts : 'array -> int list)
    (t1 : 'state)
    (arr1 : 'array)
    (index : int) <=>
      (0 : int) <= index /\ index < &(LENGTH (marked t1)) /\
      let marked1 = esm_update (marked t1) index T in
        (LENGTH marked1 = LENGTH (marked t1) /\
         esm_get_bool marked1 index = T /\
         (!j : int.
            ((0 : int) <= j /\ j < &(LENGTH (marked t1))) /\
            ~(j = index) ==>
            esm_get_bool marked1 j = esm_get_bool (marked t1) j)) ==>
        esm_result_condition nexts marked arr max_of max_arr_of elts
          t1 marked1 arr1 index`;

val esm_positive_entry_def = Define `
  esm_positive_entry
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (arr : 'state -> 'array)
    (max_of : 'state -> 63 word)
    (max_arr_of : 'state -> 63 word)
    (elts : 'array -> int list)
    (size : 'array -> int)
    (t1 : 'state)
    (x : int)
    (o4 : 63 word)
    (index : int) <=>
      esm_in_bounds (-w2i o4) /\
      !o5 : 63 word.
        w2i o5 = -w2i o4 ==>
        (0 : int) <= x /\ x < &(LENGTH (elts (arr t1))) /\
        !t_arr : 'array.
          size t_arr = size (arr t1) ==>
          size t_arr = size (arr t1) ==>
          elts t_arr = esm_update (elts (arr t1)) x (w2i o5) ==>
          esm_marking_condition nexts marked arr max_of max_arr_of elts
            t1 t_arr index`;

val esm_entry_condition_def = Define `
  esm_entry_condition
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (arr : 'state -> 'array)
    (max_of : 'state -> 63 word)
    (max_arr_of : 'state -> 63 word)
    (elts : 'array -> int list)
    (size : 'array -> int)
    (t1 : 'state)
    (x : int)
    (index : int) <=>
      !o2 : 63 word.
        w2i o2 = esm_get_int (elts (arr t1)) x ==>
        if (0 : int) <= w2i o2 then
          (0 : int) <= x /\ x < &(LENGTH (elts (arr t1))) /\
          !o4 : 63 word.
            w2i o4 = esm_get_int (elts (arr t1)) x ==>
            esm_positive_entry nexts marked arr max_of max_arr_of
              elts size t1 x o4 index
        else
          esm_marking_condition nexts marked arr max_of max_arr_of elts
            t1 (arr t1) index`;

val euler_sieve_EulerSieveImpl_set_markqtvc_statement =
  ``!nexts : 'state -> int list.
    !marked : 'state -> bool list.
    !arr : 'state -> 'array.
    !max_of : 'state -> 63 word.
    !max_arr_of : 'state -> 63 word.
    !elts : 'array -> int list.
    !size : 'array -> int.
      ((!self : 'array. esm_array_invariant elts size self) /\
       (!self : 'state.
          esm_state_invariant elts (nexts self) (marked self) (arr self)
            (w2i (max_of self)) (w2i (max_arr_of self))) /\
       (!a b : 'state.
          nexts a = nexts b /\
          marked a = marked b /\
          arr a = arr b /\
          max_of a = max_of b /\
          max_arr_of a = max_arr_of b ==>
          a = b))
      ==>
      !i : 63 word.
      !t1 : 'state.
        (0 : int) <= w2i i ==>
        w2i i <= w2i (max_of t1) ==>
        w2i i rem (2 : int) = (1 : int) ==>
        ~((2 : int) = (0 : int)) /\
        esm_in_bounds (w2i i quot (2 : int)) /\
        !x : 63 word.
          w2i x = w2i i quot (2 : int) ==>
          ((0 : int) <= w2i x /\
           w2i x < &(LENGTH (elts (arr t1)))) /\
          esm_entry_condition nexts marked arr max_of max_arr_of
            elts size t1 (w2i x) (w2i i)``;
