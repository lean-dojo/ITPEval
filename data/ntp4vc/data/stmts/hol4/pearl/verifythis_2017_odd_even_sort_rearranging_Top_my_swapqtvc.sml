(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_sort_rearranging_Top_my_swapqtvc: the
  verification condition for swapping two out-of-order integer-array entries,
  preserving the exchange relation and strictly decreasing the weighted
  entropy measure. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val odd_even_swap_to_num_def = Define `
  odd_even_swap_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val odd_even_swap_get_def = Define `
  odd_even_swap_get (a : int list) (i : int) =
    if odd_even_swap_to_num i < LENGTH a then
      EL (odd_even_swap_to_num i) a
    else
      (0 : int)`;

val odd_even_swap_sum_from_def = Define `
  (odd_even_swap_sum_from
      (f : int -> int) (start : int) 0 = (0 : int)) /\
  (odd_even_swap_sum_from f start (SUC count) =
     f start +
       odd_even_swap_sum_from
         f (start + (1 : int)) count)`;

val odd_even_swap_aux_def = Define `
  odd_even_swap_aux
      (f : int -> int) (m : int) (i : int) =
    i * (m - f i)`;

val odd_even_swap_entropy_def = Define `
  odd_even_swap_entropy (a : int list) (m : int) =
    odd_even_swap_sum_from
      (odd_even_swap_aux (odd_even_swap_get a) m)
      (0 : int)
      (LENGTH a)`;

val odd_even_swap_exchange_def = Define `
  odd_even_swap_exchange
      (before : int list) (after : int list)
      (i : int) (j : int) <=>
    after =
      LUPDATE
        (odd_even_swap_get before i)
        (odd_even_swap_to_num j)
        (LUPDATE
          (odd_even_swap_get before j)
          (odd_even_swap_to_num i)
          before)`;

val verifythis_2017_odd_even_sort_rearranging_Top_my_swapqtvc_statement =
  ``!(a : int list) (j : int) (i : int) (m : int).
      odd_even_swap_get a j < odd_even_swap_get a i ==>
      (0 : int) <= i ==>
      i < j ==>
      j < &(LENGTH a) ==>
      (0 : int) <= i /\
      i < &(LENGTH a) /\
      (0 : int) <= j /\
      j < &(LENGTH a) /\
      (!a1 : int list.
         LENGTH a1 = LENGTH a ==>
         odd_even_swap_exchange a a1 i j ==>
         odd_even_swap_exchange a a1 i j /\
         odd_even_swap_entropy a1 m <
           odd_even_swap_entropy a m)``;
