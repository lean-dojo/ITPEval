(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_sort_rearranging_Top_my_swapqtvc: swapping
  an earlier larger integer-array entry with a later smaller entry preserves
  the exchange relation and strictly decreases the entropy sum. This file
  contains no proof.
*)

let odd_even_swap_to_num = new_definition
 `odd_even_swap_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let odd_even_swap_nth = new_definition
 `odd_even_swap_nth (a:int list) (i:int) =
    if odd_even_swap_to_num i < LENGTH a
    then EL (odd_even_swap_to_num i) a
    else (&0:int)`;;

let odd_even_swap_update =
  new_recursive_definition list_RECURSION
   `(!n:num. !x:int.
       odd_even_swap_update [] n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       odd_even_swap_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (odd_even_swap_update t (PRE n) x))`;;

let odd_even_swap_array_exchange = new_definition
 `odd_even_swap_array_exchange
    (old:int list) (new:int list) (i:int) (j:int) <=>
    new =
      odd_even_swap_update
        (odd_even_swap_update
          old
          (odd_even_swap_to_num i)
          (odd_even_swap_nth old j))
        (odd_even_swap_to_num j)
        (odd_even_swap_nth old i)`;;

let odd_even_swap_entropy_from =
  new_recursive_definition list_RECURSION
   `(!m k:int.
       odd_even_swap_entropy_from [] m k = (&0:int)) /\
    (!x:int.
     !xs:int list.
     !m k:int.
       odd_even_swap_entropy_from (CONS x xs) m k =
       k * (m - x) +
       odd_even_swap_entropy_from xs m (k + (&1:int)))`;;

let odd_even_swap_entropy = new_definition
 `odd_even_swap_entropy (a:int list) (m:int) =
    odd_even_swap_entropy_from a m (&0:int)`;;

let statement =
 `!a:int list.
  !j i m:int.
    odd_even_swap_nth a j < odd_even_swap_nth a i
    ==>
    (&0:int) <= i
    ==>
    i < j
    ==>
    j < (&(LENGTH a):int)
    ==>
    ((&0:int) <= i /\
     i < (&(LENGTH a):int) /\
     (&0:int) <= j /\
     j < (&(LENGTH a):int) /\
     (!a1:int list.
        LENGTH a1 = LENGTH a
        ==>
        odd_even_swap_array_exchange a a1 i j
        ==>
        odd_even_swap_array_exchange a a1 i j /\
        odd_even_swap_entropy a1 m < odd_even_swap_entropy a m))`;;
