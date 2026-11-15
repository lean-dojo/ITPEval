(* Statement-only formalization of ntp4vc artifact pearl/euler_sieve_EulerSieveImpl_createqtvc: the verification condition for constructing the signed 63-bit Euler-sieve state, including its initialized successor and marking lists, invariant-bounded auxiliary arrays, loop invariants, and returned-state postconditions. This file contains no proof. *)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val es_to_num_def = Define `
  es_to_num (z : int) = if z < 0 then 0 else Num z`;

val es_get_int_def = Define `
  es_get_int (xs : int list) (i : int) =
    if es_to_num i < LENGTH xs then EL (es_to_num i) xs else (0 : int)`;

val es_get_bool_def = Define `
  es_get_bool (xs : bool list) (i : int) =
    if es_to_num i < LENGTH xs then EL (es_to_num i) xs else F`;

val es_in_bounds_def = Define `
  es_in_bounds (z : int) <=>
    (-4611686018427387904 : int) <= z /\
    z <= (4611686018427387903 : int)`;

val es_array_invariant_def = Define `
  es_array_invariant
    (elts : 'array -> int list)
    (size : 'array -> int)
    (self : 'array) <=>
      (0 : int) <= size self /\
      size self = &(LENGTH (elts self)) /\
      &(LENGTH (elts self)) <= (4611686018427387903 : int) /\
      !i : int.
        (0 : int) <= i /\ i < &(LENGTH (elts self)) ==>
        es_in_bounds (es_get_int (elts self) i)`;

val es_inv_nexts_def = Define `
  es_inv_nexts (nexts : int list) (n : int) <=>
    !i : int.
      (0 : int) <= i /\ i < n ==>
      i < es_get_int nexts i /\ es_get_int nexts i <= n`;

val es_all_eliminated_marked_def = Define `
  es_all_eliminated_marked (marked : bool list) (nexts : int list) <=>
    LENGTH marked = LENGTH nexts /\
    !i : int.
      (0 : int) <= i /\ i < &(LENGTH marked) ==>
      !j : int.
        i < j /\ j < es_get_int nexts i ==>
        es_get_bool marked j = T`;

val es_fc_def = Define `
  es_fc (max1 : 63 word) (i : int) =
    if i = w2i max1 then w2i max1 + (1 : int)
    else if i = w2i max1 - (1 : int) then
      if i rem (2 : int) = (0 : int) then w2i max1
      else w2i max1 + (1 : int)
    else if i < (3 : int) \/ i rem (2 : int) = (0 : int) then
      i + (1 : int)
    else i + (2 : int)`;

val es_o1_def = Define `
  es_o1 (i : int) <=>
    i = (0 : int) \/ i = (1 : int) \/
    (2 : int) < i /\ i rem (2 : int) = (0 : int)`;

val es_fc1_def = Define `
  es_fc1 (max1 : 63 word) (len_arr : 63 word) (i : int) =
    if i = w2i len_arr - (1 : int) then w2i max1 + (1 : int)
    else if i = (0 : int) then -(2 : int)
    else (2 : int) * i + (3 : int)`;

val es_state_invariant_values_def = Define `
  es_state_invariant_values
    (elts : 'array -> int list)
    (nexts1 : int list)
    (marked1 : bool list)
    (arr1 : 'array)
    (max1 : 63 word)
    (o8 : 63 word) <=>
      (w2i max1 < (4611686018427387903 : int) /\
       (3 : int) <= w2i max1) /\
      (LENGTH nexts1 = LENGTH marked1 /\
       &(LENGTH marked1) = w2i max1 + (1 : int)) /\
      (w2i max1 - (1 : int)) quot (2 : int) = w2i o8 /\
      &(LENGTH (elts arr1)) = w2i o8 + (1 : int) /\
      es_inv_nexts nexts1 (&(LENGTH nexts1)) /\
      es_all_eliminated_marked marked1 nexts1 /\
      (!i : int.
         (3 : int) <= i /\ i <= w2i max1 ==>
         i rem (2 : int) = (0 : int) ==>
         es_get_bool marked1 i = T) /\
      (!i : int.
         (3 : int) <= i /\ i < w2i max1 - (1 : int) ==>
         i rem (2 : int) = (1 : int) ==>
         es_get_int nexts1 i rem (2 : int) = (1 : int) \/
         es_get_int nexts1 i = w2i max1 + (1 : int)) /\
      (es_get_int nexts1 (w2i max1) = w2i max1 + (1 : int) /\
       ((w2i max1 - (1 : int)) rem (2 : int) = (0 : int) ==>
        es_get_int nexts1 (w2i max1 - (1 : int)) = w2i max1)) /\
      ((w2i max1 - (1 : int)) rem (2 : int) = (1 : int) ==>
       es_get_int nexts1 (w2i max1 - (1 : int)) =
         w2i max1 + (1 : int)) /\
      (!i : int.
         (0 : int) <= i /\ i <= w2i o8 ==>
         -(w2i max1 + (1 : int)) <= es_get_int (elts arr1) i /\
         es_get_int (elts arr1) i <= w2i max1 + (1 : int)) /\
      (!i : int.
         (0 : int) <= i /\ i <= w2i o8 ==>
         (es_get_bool marked1 ((2 : int) * i + (1 : int)) = T <=>
          es_get_int (elts arr1) i < (0 : int))) /\
      (!i : int.
         (0 : int) <= i /\ i <= w2i o8 ==>
         ~(es_get_bool marked1 ((2 : int) * i + (1 : int)) = T) ==>
         es_get_int (elts arr1) i =
           es_get_int nexts1 ((2 : int) * i + (1 : int))) /\
      (!i : int.
         (0 : int) <= i /\ i <= w2i o8 ==>
         es_get_bool marked1 ((2 : int) * i + (1 : int)) = T ==>
         es_get_int (elts arr1) i =
           -es_get_int nexts1 ((2 : int) * i + (1 : int))) /\
      (!i : int.
         (0 : int) <= i /\ i <= w2i o8 ==>
         (i < ABS (es_get_int (elts arr1) i) quot (2 : int) /\
          ABS (es_get_int (elts arr1) i) quot (2 : int) <=
            w2i o8 + (1 : int)) /\
         ABS (es_get_int (elts arr1) i) <= w2i max1 + (1 : int)) /\
      (!i j : int.
         (0 : int) <= i /\ i <= w2i o8 ==>
         i < j /\ j < ABS (es_get_int (elts arr1) i) quot (2 : int) ==>
         es_get_int (elts arr1) j < (0 : int))`;

val es_state_invariant_def = Define `
  es_state_invariant
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (arr : 'state -> 'array)
    (max_of : 'state -> 63 word)
    (max_arr_of : 'state -> 63 word)
    (elts : 'array -> int list)
    (self : 'state) <=>
      es_state_invariant_values elts
        (nexts self) (marked self) (arr self)
        (max_of self) (max_arr_of self)`;

val es_finish_def = Define `
  es_finish
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (arr : 'state -> 'array)
    (max_of : 'state -> 63 word)
    (max_arr_of : 'state -> 63 word)
    (elts : 'array -> int list)
    (nexts1 : int list)
    (marked1 : bool list)
    (arr1 : 'array)
    (max1 : 63 word)
    (o8 : 63 word) <=>
      es_state_invariant_values elts
        nexts1 marked1 arr1 max1 o8 /\
      !result : 'state.
        nexts result = nexts1 /\
        marked result = marked1 /\
        arr result = arr1 /\
        max_of result = max1 /\
        max_arr_of result = o8 ==>
        max_of result = max1 /\
        (((es_get_bool (marked result) (0 : int) =
            es_get_bool (marked result) (1 : int) /\
           es_get_bool (marked result) (1 : int) = T) /\
          ~(es_get_bool (marked result) (2 : int) = T)) /\
         (!i : int.
            (1 : int) <= i /\
            i <= (w2i max1 - (1 : int)) quot (2 : int) ==>
            ~(es_get_bool (marked result)
                ((2 : int) * i + (1 : int)) = T)) /\
         (!i : int.
            (2 : int) <= i /\
            i <= (w2i max1 + (1 : int)) quot (2 : int) ==>
            (2 : int) * i <= w2i max1 ==>
            es_get_bool (marked result) ((2 : int) * i) = T) /\
         (!i : int.
            (1 : int) <= i /\
            i <= (w2i max1 - (1 : int)) quot (2 : int) ==>
            (2 : int) * i + (1 : int) < w2i max1 - (1 : int) ==>
            es_get_int (nexts result) ((2 : int) * i + (1 : int)) =
              (2 : int) * i + (3 : int)) /\
         (!i : int.
            (2 : int) <= i /\
            i <= (w2i max1 - (1 : int)) quot (2 : int) ==>
            (2 : int) * i < w2i max1 - (1 : int) ==>
            es_get_int (nexts result) ((2 : int) * i) =
              (2 : int) * i + (1 : int)) /\
         (!i : int.
            (0 : int) <= i /\ i <= w2i max1 ==>
            es_get_bool (marked result) i = T ==>
            i < (2 : int) \/ ?k : int. i = (2 : int) * k))`;

val euler_sieve_EulerSieveImpl_createqtvc_statement =
  ``!nexts : 'state -> int list.
    !marked : 'state -> bool list.
    !arr : 'state -> 'array.
    !max_of : 'state -> 63 word.
    !max_arr_of : 'state -> 63 word.
    !elts : 'array -> int list.
    !size : 'array -> int.
      (!self : 'array. es_array_invariant elts size self) ==>
      (!self : 'state.
         es_state_invariant
           nexts marked arr max_of max_arr_of elts self) ==>
      (!a b : 'state.
         nexts a = nexts b /\
         marked a = marked b /\
         arr a = arr b /\
         max_of a = max_of b /\
         max_arr_of a = max_arr_of b ==>
         a = b) ==>
      !max1 : 63 word.
        w2i max1 < (4611686018427387903 : int) ==>
        (3 : int) <= w2i max1 ==>
      let len = w2i max1 + (1 : int) in
        es_in_bounds (w2i max1 - (1 : int)) /\
        !o2 : 63 word.
          w2i o2 = w2i max1 - (1 : int) ==>
          (~((2 : int) = (0 : int)) /\
           es_in_bounds (w2i o2 quot (2 : int))) /\
          !o3 : 63 word.
            w2i o3 = w2i o2 quot (2 : int) ==>
            es_in_bounds (w2i o3 + (1 : int)) /\
            !len_arr : 63 word.
              w2i len_arr = w2i o3 + (1 : int) ==>
              let nexts1 =
                GENLIST (\n. es_fc max1 (&n)) (es_to_num len)
              in
                (0 : int) <= len /\
                (&(LENGTH nexts1) = len /\
                 (!i : int.
                    (0 : int) <= i /\ i < len ==>
                    es_get_int nexts1 i = es_fc max1 i) ==>
                 (!i : int.
                    ~(i = (0 : int)) ==>
                    ~(i = (1 : int)) ==>
                    (2 : int) < i ==>
                    ~((2 : int) = (0 : int))) /\
                 let marked1 =
                   GENLIST (\n. es_o1 (&n)) (es_to_num len)
                 in
                   (0 : int) <= len /\
                   (&(LENGTH marked1) = len /\
                    (!i : int.
                       (0 : int) <= i /\ i < len ==>
                       es_get_bool marked1 i = es_o1 i) ==>
                    (0 : int) <= w2i len_arr /\
                    !arr1 : 'array.
                      ((!i : int.
                          (0 : int) <= i /\ i < w2i len_arr ==>
                          es_get_int (elts arr1) i =
                            w2i (-(2w : 63 word))) /\
                       &(LENGTH (elts arr1)) = w2i len_arr) ==>
                      es_in_bounds (w2i len_arr - (1 : int)) /\
                      !o6 : 63 word.
                        w2i o6 = w2i len_arr - (1 : int) ==>
                        (((1 : int) <= w2i o6 + (1 : int) ==>
                          (!j : int.
                             (0 : int) <= j /\ j < (1 : int) ==>
                             es_get_int (elts arr1) j =
                               es_fc1 max1 len_arr j) /\
                          !arr2 : 'array.
                            size arr2 = size arr1 ==>
                            ((!i : 63 word.
                               let i1 = w2i i in
                                 (((1 : int) <= i1 /\
                                   i1 <= w2i o6) /\
                                  (!j : int.
                                     (0 : int) <= j /\ j < i1 ==>
                                     es_get_int (elts arr2) j =
                                       es_fc1 max1 len_arr j)) ==>
                                 es_in_bounds
                                   (w2i len_arr - (1 : int)) /\
                                 !o7 : 63 word.
                                   w2i o7 =
                                     w2i len_arr - (1 : int) ==>
                                   (w2i i = w2i o7 ==> i = o7) ==>
                                   ((if i = o7 then
                                       es_in_bounds
                                         (w2i max1 + (1 : int))
                                     else
                                       es_in_bounds
                                         ((2 : int) * w2i i) /\
                                       !o8 : 63 word.
                                         w2i o8 =
                                           (2 : int) * w2i i ==>
                                         es_in_bounds
                                           (w2i o8 + (3 : int))) /\
                                    !o8 : 63 word.
                                      (if i = o7 then
                                         w2i o8 =
                                           w2i max1 + (1 : int)
                                       else
                                         ?o9 : 63 word.
                                           w2i o9 =
                                             (2 : int) * w2i i /\
                                           w2i o8 =
                                             w2i o9 + (3 : int)) ==>
                                      ((0 : int) <= w2i i /\
                                       w2i i <
                                         &(LENGTH (elts arr2))) /\
                                      !arr3 : 'array.
                                        size arr3 = size arr2 ==>
                                        elts arr3 =
                                          LUPDATE (w2i o8)
                                            (es_to_num (w2i i))
                                            (elts arr2) ==>
                                        !j : int.
                                          (0 : int) <= j /\
                                          j < i1 + (1 : int) ==>
                                          es_get_int (elts arr3) j =
                                            es_fc1 max1 len_arr j)) /\
                             ((!j : int.
                                 (0 : int) <= j /\
                                 j < w2i o6 + (1 : int) ==>
                                 es_get_int (elts arr2) j =
                                   es_fc1 max1 len_arr j) ==>
                              es_in_bounds
                                (w2i max1 - (1 : int)) /\
                              !o7 : 63 word.
                                w2i o7 =
                                  w2i max1 - (1 : int) ==>
                                (~((2 : int) = (0 : int)) /\
                                 es_in_bounds
                                   (w2i o7 quot (2 : int))) /\
                                !o8 : 63 word.
                                  w2i o8 =
                                    w2i o7 quot (2 : int) ==>
                                  es_finish nexts marked arr max_of
                                    max_arr_of elts nexts1 marked1
                                    arr2 max1 o8))) /\
                         (w2i o6 + (1 : int) < (1 : int) ==>
                          es_in_bounds
                            (w2i max1 - (1 : int)) /\
                          !o7 : 63 word.
                            w2i o7 = w2i max1 - (1 : int) ==>
                            (~((2 : int) = (0 : int)) /\
                             es_in_bounds
                               (w2i o7 quot (2 : int))) /\
                            !o8 : 63 word.
                              w2i o8 = w2i o7 quot (2 : int) ==>
                              es_finish nexts marked arr max_of
                                max_arr_of elts nexts1 marked1
                                arr1 max1 o8))))``;
