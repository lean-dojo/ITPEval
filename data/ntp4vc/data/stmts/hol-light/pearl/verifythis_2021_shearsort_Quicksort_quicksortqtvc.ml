(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_Quicksort_quicksortqtvc: the full-array
  quicksort verification condition, requiring the resulting integer array
  to be sorted and a permutation of the input. This file contains no proof.
*)

let shearsort_quicksort_to_num = new_definition
 `shearsort_quicksort_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let shearsort_quicksort_nth = new_definition
 `shearsort_quicksort_nth (a:int list) (i:int) =
    if shearsort_quicksort_to_num i < LENGTH a
    then EL (shearsort_quicksort_to_num i) a
    else (&0:int)`;;

let shearsort_quicksort_permut_sub_prime = new_definition
 `shearsort_quicksort_permut_sub_prime
    (a1:int list) (a2:int list) (l:num) (u:num) <=>
    LENGTH a1 = LENGTH a2 /\
    (!k:num.
       k < l /\ k < LENGTH a1
       ==> EL k a1 = EL k a2) /\
    (!k:num.
       u <= k /\ k < LENGTH a1
       ==> EL k a1 = EL k a2) /\
    (!v:int.
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a2 /\ EL k a2 = v})`;;

let shearsort_quicksort_sorted_sub = new_definition
 `shearsort_quicksort_sorted_sub (a:int list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 <= i2 /\ i2 < u
      ==> shearsort_quicksort_nth a i1 <=
          shearsort_quicksort_nth a i2`;;

let shearsort_quicksort_sorted = new_definition
 `shearsort_quicksort_sorted (a:int list) <=>
    shearsort_quicksort_sorted_sub
      a (&0:int) (&(LENGTH a):int)`;;

let shearsort_quicksort_permutation = new_definition
 `shearsort_quicksort_permutation (a1:int list) (a2:int list) <=>
    LENGTH a1 = LENGTH a2 /\
    (!v:int.
       CARD {k:num | k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num | k < LENGTH a2 /\ EL k a2 = v})`;;

let shearsort_quicksort_qs_partition = new_definition
 `shearsort_quicksort_qs_partition
    (a1:int list) (a2:int list)
    (l:int) (m:int) (r:int) (v:int) <=>
    shearsort_quicksort_permut_sub_prime
      a1 a2
      (shearsort_quicksort_to_num l)
      (shearsort_quicksort_to_num r) /\
    (!j:int.
       l <= j /\ j < m
       ==> shearsort_quicksort_nth a2 j < v) /\
    (!j:int.
       m < j /\ j < r
       ==> v <= shearsort_quicksort_nth a2 j) /\
    shearsort_quicksort_nth a2 m = v`;;

let statement =
 `!a:int list.
    let o1 = (&(LENGTH a):int) in
    (((&0:int) <= (&0:int) /\
      (&0:int) <= o1 /\
      o1 <= (&(LENGTH a):int)) /\
     (!a1:int list.
        LENGTH a1 = LENGTH a
        ==>
        shearsort_quicksort_sorted_sub a1 (&0:int) o1 /\
        shearsort_quicksort_permut_sub_prime
          a a1 0 (shearsort_quicksort_to_num o1)
        ==>
        shearsort_quicksort_sorted a1 /\
        shearsort_quicksort_permutation a a1))`;;
