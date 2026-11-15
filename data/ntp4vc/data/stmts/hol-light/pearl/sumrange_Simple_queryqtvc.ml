(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_Simple_queryqtvc: the verification condition for a linear
  integer range-sum query, including loop initialization, invariant
  preservation, and exit obligations for a half-open interval. This file
  contains no proof.
*)

let sumrange_simple_query_to_num = new_definition
 `sumrange_simple_query_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let sumrange_simple_query_nth = new_definition
 `sumrange_simple_query_nth (a:int list) (i:int) =
    if sumrange_simple_query_to_num i < LENGTH a
    then EL (sumrange_simple_query_to_num i) a
    else (&0:int)`;;

let sumrange_simple_query_sum_nat =
  new_recursive_definition num_RECURSION
   `(!a:int list. !lower:int.
       sumrange_simple_query_sum_nat a lower 0 = (&0:int)) /\
    (!a:int list. !lower:int. !n:num.
       sumrange_simple_query_sum_nat a lower (SUC n) =
       sumrange_simple_query_nth a lower +
       sumrange_simple_query_sum_nat
         a (lower + (&1:int)) n)`;;

let sumrange_simple_query_sum = new_definition
 `sumrange_simple_query_sum
    (a:int list) (lower:int) (upper:int) =
    sumrange_simple_query_sum_nat a lower
      (sumrange_simple_query_to_num (upper - lower))`;;

let statement =
 `!i j:int. !a:int list.
    (&0:int) <= i
    ==>
    i <= j
    ==>
    j <= (&(LENGTH a):int)
    ==>
    let o1 = j - (&1:int) in
    (i <= o1 + (&1:int)
     ==>
     (&0:int) = sumrange_simple_query_sum a i i /\
     (!s:int.
        (!k:int.
           ((i <= k /\ k <= o1) /\
            s = sumrange_simple_query_sum a i k)
           ==>
           ((&0:int) <= k /\ k < (&(LENGTH a):int)) /\
           s + sumrange_simple_query_nth a k =
             sumrange_simple_query_sum a i (k + (&1:int))) /\
        (s = sumrange_simple_query_sum a i (o1 + (&1:int))
         ==>
         s = sumrange_simple_query_sum a i j)))
    /\
    (o1 + (&1:int) < i
     ==>
     (&0:int) = sumrange_simple_query_sum a i j)`;;
