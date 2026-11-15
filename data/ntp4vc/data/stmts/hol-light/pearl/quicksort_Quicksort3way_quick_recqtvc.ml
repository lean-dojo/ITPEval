(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/quicksort_Quicksort3way_quick_recqtvc: the recursive three-way
  quicksort verification condition, including partition invariants, swaps,
  termination measures, recursive sortedness, and subarray permutation.
  This file contains no proof.
*)

let quicksort3way_to_num = new_definition
 `quicksort3way_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let quicksort3way_nth = new_definition
 `quicksort3way_nth (a:int list) (i:int) =
    if quicksort3way_to_num i < LENGTH a
    then EL (quicksort3way_to_num i) a
    else (&0:int)`;;

let quicksort3way_permut_sub_prime = new_definition
 `quicksort3way_permut_sub_prime
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

let quicksort3way_exchange = new_definition
 `quicksort3way_exchange
    (a1:int list) (a2:int list) (i:int) (j:int) <=>
    !k:int.
      quicksort3way_nth a2 k =
      if k = i then quicksort3way_nth a1 j
      else if k = j then quicksort3way_nth a1 i
      else quicksort3way_nth a1 k`;;

let quicksort3way_sorted_sub = new_definition
 `quicksort3way_sorted_sub (a:int list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 <= i2 /\ i2 < u
      ==> quicksort3way_nth a i1 <= quicksort3way_nth a i2`;;

let quicksort3way_qs_partition = new_definition
 `quicksort3way_qs_partition
    (a1:int list) (a2:int list)
    (l:int) (ml:int) (mr:int) (r:int) (v:int) <=>
    quicksort3way_permut_sub_prime
      a1 a2 (quicksort3way_to_num l) (quicksort3way_to_num r) /\
    (!j:int.
       l <= j /\ j < ml
       ==> quicksort3way_nth a2 j < v) /\
    (!j:int.
       ml <= j /\ j < mr
       ==> quicksort3way_nth a2 j = v) /\
    (!j:int.
       mr <= j /\ j < r
       ==> v < quicksort3way_nth a2 j)`;;

let statement =
 `!l r:int. !a:int list.
    (&0:int) <= l
    ==>
    l <= r
    ==>
    r <= (&(LENGTH a):int)
    ==>
    if l + (&1:int) < r then
      ((&0:int) <= l /\ l < (&(LENGTH a):int)) /\
      (let v = quicksort3way_nth a l in
       let o1 = l + (&1:int) in
       ((l <= l /\ l < o1 /\ o1 <= r /\ r <= r) /\
        (!j:int.
           l <= j /\ j < l
           ==> quicksort3way_nth a j < v) /\
        (!j:int.
           l <= j /\ j < o1
           ==> quicksort3way_nth a j = v) /\
        (!j:int.
           r <= j /\ j < r
           ==> v < quicksort3way_nth a j) /\
        quicksort3way_permut_sub_prime
          a a (quicksort3way_to_num l) (quicksort3way_to_num r)) /\
       (!i mr ml:int. !a1:int list.
          LENGTH a1 = LENGTH a
          ==>
          (l <= ml /\ ml < i /\ i <= mr /\ mr <= r) /\
          (!j:int.
             l <= j /\ j < ml
             ==> quicksort3way_nth a1 j < v) /\
          (!j:int.
             ml <= j /\ j < i
             ==> quicksort3way_nth a1 j = v) /\
          (!j:int.
             mr <= j /\ j < r
             ==> v < quicksort3way_nth a1 j) /\
          quicksort3way_permut_sub_prime
            a a1 (quicksort3way_to_num l) (quicksort3way_to_num r)
          ==>
          if i < mr then
            ((&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
            (if quicksort3way_nth a1 i < v then
               (((&0:int) <= ml /\ ml < (&(LENGTH a1):int)) /\
                (&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
               (!a2:int list.
                  LENGTH a2 = LENGTH a1
                  ==>
                  quicksort3way_exchange a1 a2 ml i
                  ==>
                  ((&0:int) <= mr - i /\
                   mr - (i + (&1:int)) < mr - i) /\
                  (l <= ml + (&1:int) /\
                   ml + (&1:int) < i + (&1:int) /\
                   i + (&1:int) <= mr /\
                   mr <= r) /\
                  (!j:int.
                     l <= j /\ j < ml + (&1:int)
                     ==> quicksort3way_nth a2 j < v) /\
                  (!j:int.
                     ml + (&1:int) <= j /\ j < i + (&1:int)
                     ==> quicksort3way_nth a2 j = v) /\
                  (!j:int.
                     mr <= j /\ j < r
                     ==> v < quicksort3way_nth a2 j) /\
                  quicksort3way_permut_sub_prime
                    a a2
                    (quicksort3way_to_num l)
                    (quicksort3way_to_num r))
             else
               ((&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
               (if v < quicksort3way_nth a1 i then
                  (((&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
                   (&0:int) <= mr - (&1:int) /\
                   mr - (&1:int) < (&(LENGTH a1):int)) /\
                  (!a2:int list.
                     LENGTH a2 = LENGTH a1
                     ==>
                     quicksort3way_exchange a1 a2 i (mr - (&1:int))
                     ==>
                     ((&0:int) <= mr - i /\
                      mr - (&1:int) - i < mr - i) /\
                     (l <= ml /\
                      ml < i /\
                      i <= mr - (&1:int) /\
                      mr - (&1:int) <= r) /\
                     (!j:int.
                        l <= j /\ j < ml
                        ==> quicksort3way_nth a2 j < v) /\
                     (!j:int.
                        ml <= j /\ j < i
                        ==> quicksort3way_nth a2 j = v) /\
                     (!j:int.
                        mr - (&1:int) <= j /\ j < r
                        ==> v < quicksort3way_nth a2 j) /\
                     quicksort3way_permut_sub_prime
                       a a2
                       (quicksort3way_to_num l)
                       (quicksort3way_to_num r))
                else
                  ((&0:int) <= mr - i /\
                   mr - (i + (&1:int)) < mr - i) /\
                  (l <= ml /\
                   ml < i + (&1:int) /\
                   i + (&1:int) <= mr /\
                   mr <= r) /\
                  (!j:int.
                     l <= j /\ j < ml
                     ==> quicksort3way_nth a1 j < v) /\
                  (!j:int.
                     ml <= j /\ j < i + (&1:int)
                     ==> quicksort3way_nth a1 j = v) /\
                  (!j:int.
                     mr <= j /\ j < r
                     ==> v < quicksort3way_nth a1 j) /\
                  quicksort3way_permut_sub_prime
                    a a1
                    (quicksort3way_to_num l)
                    (quicksort3way_to_num r)))
          else
            (((&0:int) <= r - l /\ ml - l < r - l) /\
             (&0:int) <= l /\
             l <= ml /\
             ml <= (&(LENGTH a1):int)) /\
            (!a2:int list.
               LENGTH a2 = LENGTH a1
               ==>
               quicksort3way_sorted_sub a2 l ml /\
               quicksort3way_permut_sub_prime
                 a1 a2
                 (quicksort3way_to_num l)
                 (quicksort3way_to_num ml)
               ==>
               (((&0:int) <= r - l /\ r - mr < r - l) /\
                (&0:int) <= mr /\
                mr <= r /\
                r <= (&(LENGTH a2):int)) /\
               (!a3:int list.
                  LENGTH a3 = LENGTH a2
                  ==>
                  quicksort3way_sorted_sub a3 mr r /\
                  quicksort3way_permut_sub_prime
                    a2 a3
                    (quicksort3way_to_num mr)
                    (quicksort3way_to_num r)
                  ==>
                  quicksort3way_sorted_sub a3 l r /\
                  quicksort3way_permut_sub_prime
                    a a3
                    (quicksort3way_to_num l)
                    (quicksort3way_to_num r)))))
    else
      quicksort3way_sorted_sub a l r /\
      quicksort3way_permut_sub_prime
        a a (quicksort3way_to_num l) (quicksort3way_to_num r)`;;
