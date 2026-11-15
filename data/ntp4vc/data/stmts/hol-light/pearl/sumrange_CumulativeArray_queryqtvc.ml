(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeArray_queryqtvc: the verification condition for
  querying a cumulative integer array, including index bounds and the
  equality between a prefix-sum difference and the corresponding half-open
  range sum. This file contains no proof.
*)

let sumrange_query_to_num = new_definition
 `sumrange_query_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let sumrange_query_nth = new_definition
 `sumrange_query_nth (a:int list) (i:int) =
    if sumrange_query_to_num i < LENGTH a
    then EL (sumrange_query_to_num i) a
    else (&0:int)`;;

let sumrange_query_sum_nat =
  new_recursive_definition num_RECURSION
   `(!a:int list. !lower:int.
       sumrange_query_sum_nat a lower 0 = (&0:int)) /\
    (!a:int list. !lower:int. !n:num.
       sumrange_query_sum_nat a lower (SUC n) =
       sumrange_query_nth a lower +
       sumrange_query_sum_nat a (lower + (&1:int)) n)`;;

let sumrange_query_sum = new_definition
 `sumrange_query_sum (a:int list) (lower:int) (upper:int) =
    sumrange_query_sum_nat a lower
      (sumrange_query_to_num (upper - lower))`;;

let sumrange_query_is_cumulative_array_for = new_definition
 `sumrange_query_is_cumulative_array_for
    (c:int list) (a:int list) <=>
    (&(LENGTH c):int) = (&(LENGTH a):int) + (&1:int) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH c):int)
       ==> sumrange_query_nth c i =
           sumrange_query_sum a (&0:int) i)`;;

let statement =
 `!c a:int list. !i j:int.
    sumrange_query_is_cumulative_array_for c a
    ==>
    (&0:int) <= i
    ==>
    i <= j
    ==>
    j < (&(LENGTH c):int)
    ==>
    (&0:int) <= i /\
    i < (&(LENGTH c):int) /\
    (&0:int) <= j /\
    j < (&(LENGTH c):int) /\
    sumrange_query_nth c j - sumrange_query_nth c i =
    sumrange_query_sum a i j`;;
