(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/quicksort_Shuffle_shuffleqtvc: the verification condition for
  Knuth's shuffle of an integer array, requiring each bounded swap to
  preserve permutation of the original array. This file contains no proof.
*)

let shuffle_to_num = new_definition
 `shuffle_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let shuffle_nth = new_definition
 `shuffle_nth (a:int list) (i:int) =
    if shuffle_to_num i < LENGTH a
    then EL (shuffle_to_num i) a
    else (&0:int)`;;

let shuffle_set =
  new_recursive_definition list_RECURSION
   `(!n:num. !x:int. shuffle_set [] n x = []) /\
    (!h:int. !t:int list. !n:num. !x:int.
       shuffle_set (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (shuffle_set t (PRE n) x))`;;

let shuffle_exchange = new_definition
 `shuffle_exchange
    (before:int list) (after:int list) (i:int) (j:int) <=>
    after =
      shuffle_set
        (shuffle_set before (shuffle_to_num i) (shuffle_nth before j))
        (shuffle_to_num j)
        (shuffle_nth before i)`;;

let shuffle_permutation = new_definition
 `shuffle_permutation (a1:int list) (a2:int list) <=>
    LENGTH a1 = LENGTH a2 /\
    (!v:int.
       CARD {k:num | k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num | k < LENGTH a2 /\ EL k a2 = v})`;;

let statement =
 `!a:int list.
    let o1 = (&(LENGTH a):int) - (&1:int) in
    (((&1:int) <= o1 + (&1:int)
      ==>
      shuffle_permutation a a /\
      (!a1:int list.
         LENGTH a1 = LENGTH a
         ==>
         !i:int.
           (((&1:int) <= i /\ i <= o1) /\
            shuffle_permutation a a1)
           ==>
           let o2 = i + (&1:int) in
           (&0:int) < o2 /\
           (!o3:int.
              (&0:int) <= o3 /\ o3 < o2
              ==>
              (((&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
               (&0:int) <= o3 /\ o3 < (&(LENGTH a1):int)) /\
              (!a2:int list.
                 LENGTH a2 = LENGTH a1
                 ==>
                 shuffle_exchange a1 a2 i o3
                 ==>
                 shuffle_permutation a a2)))) /\
     (o1 + (&1:int) < (&1:int)
      ==>
      shuffle_permutation a a))`;;
