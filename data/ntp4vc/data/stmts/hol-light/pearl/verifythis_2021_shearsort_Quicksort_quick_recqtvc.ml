(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_Quicksort_quick_recqtvc: the recursive
  Bentley-style quicksort verification condition, including partition-loop
  invariants, swaps, recursively sorted subranges, and subarray permutations.
  This file contains no proof.
*)

let quicksort_to_num = new_definition
 `quicksort_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let quicksort_nth = new_definition
 `quicksort_nth (a:int list) (i:int) =
    if quicksort_to_num i < LENGTH a
    then EL (quicksort_to_num i) a
    else (&0:int)`;;

let quicksort_permut_sub_prime = new_definition
 `quicksort_permut_sub_prime
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

let quicksort_exchange = new_definition
 `quicksort_exchange
    (a1:int list) (a2:int list) (i:int) (j:int) <=>
    !k:int.
      (&0:int) <= k /\ k < (&(LENGTH a2):int)
      ==>
      quicksort_nth a2 k =
      if k = i then quicksort_nth a1 j
      else if k = j then quicksort_nth a1 i
      else quicksort_nth a1 k`;;

let quicksort_sorted_sub = new_definition
 `quicksort_sorted_sub (a:int list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 <= i2 /\ i2 < u
      ==> quicksort_nth a i1 <= quicksort_nth a i2`;;

let quicksort_qs_partition = new_definition
 `quicksort_qs_partition
    (a1:int list) (a2:int list)
    (l:int) (m:int) (r:int) (v:int) <=>
    quicksort_permut_sub_prime
      a1 a2 (quicksort_to_num l) (quicksort_to_num r) /\
    (!j:int.
       l <= j /\ j < m
       ==> quicksort_nth a2 j < v) /\
    (!j:int.
       m < j /\ j < r
       ==> v <= quicksort_nth a2 j) /\
    quicksort_nth a2 m = v`;;

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
      (let v = quicksort_nth a l in
       let o1 = r - (&1:int) in
       let o2 = l + (&1:int) in
       (o2 <= o1 + (&1:int)
        ==>
        ((quicksort_nth a l = v /\ l <= l /\ l < o2) /\
         (!j:int.
            l < j /\ j <= l
            ==> quicksort_nth a j < v) /\
         (!j:int.
            l < j /\ j < o2
            ==> v <= quicksort_nth a j) /\
         quicksort_permut_sub_prime
           a a (quicksort_to_num l) (quicksort_to_num r)) /\
        (!m:int. !a1:int list.
           LENGTH a1 = LENGTH a
           ==>
           (!i:int.
              (o2 <= i /\ i <= o1) /\
              (quicksort_nth a1 l = v /\ l <= m /\ m < i) /\
              (!j:int.
                 l < j /\ j <= m
                 ==> quicksort_nth a1 j < v) /\
              (!j:int.
                 m < j /\ j < i
                 ==> v <= quicksort_nth a1 j) /\
              quicksort_permut_sub_prime
                a a1 (quicksort_to_num l) (quicksort_to_num r)
              ==>
              ((&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
              (if quicksort_nth a1 i < v then
                 (((&0:int) <= i /\ i < (&(LENGTH a1):int)) /\
                  (&0:int) <= m + (&1:int) /\
                  m + (&1:int) < (&(LENGTH a1):int)) /\
                 (!a2:int list.
                    LENGTH a2 = LENGTH a1
                    ==>
                    quicksort_exchange a1 a2 i (m + (&1:int))
                    ==>
                    (quicksort_nth a2 l = v /\
                     l <= m + (&1:int) /\
                     m + (&1:int) < i + (&1:int)) /\
                    (!j:int.
                       l < j /\ j <= m + (&1:int)
                       ==> quicksort_nth a2 j < v) /\
                    (!j:int.
                       m + (&1:int) < j /\ j < i + (&1:int)
                       ==> v <= quicksort_nth a2 j) /\
                    quicksort_permut_sub_prime
                      a a2
                      (quicksort_to_num l)
                      (quicksort_to_num r))
               else
                 (quicksort_nth a1 l = v /\
                  l <= m /\
                  m < i + (&1:int)) /\
                 (!j:int.
                    l < j /\ j <= m
                    ==> quicksort_nth a1 j < v) /\
                 (!j:int.
                    m < j /\ j < i + (&1:int)
                    ==> v <= quicksort_nth a1 j) /\
                 quicksort_permut_sub_prime
                   a a1
                   (quicksort_to_num l)
                   (quicksort_to_num r))) /\
           ((quicksort_nth a1 l = v /\
             l <= m /\
             m < o1 + (&1:int)) /\
            (!j:int.
               l < j /\ j <= m
               ==> quicksort_nth a1 j < v) /\
            (!j:int.
               m < j /\ j < o1 + (&1:int)
               ==> v <= quicksort_nth a1 j) /\
            quicksort_permut_sub_prime
              a a1 (quicksort_to_num l) (quicksort_to_num r)
            ==>
            (((&0:int) <= l /\ l < (&(LENGTH a1):int)) /\
             (&0:int) <= m /\ m < (&(LENGTH a1):int)) /\
            (!a2:int list.
               LENGTH a2 = LENGTH a1
               ==>
               quicksort_exchange a1 a2 l m
               ==>
               (((&0:int) <= r - l /\ m - l < r - l) /\
                (&0:int) <= l /\
                l <= m /\
                m <= (&(LENGTH a2):int)) /\
               (!a3:int list.
                  LENGTH a3 = LENGTH a2
                  ==>
                  quicksort_sorted_sub a3 l m /\
                  quicksort_permut_sub_prime
                    a2 a3
                    (quicksort_to_num l)
                    (quicksort_to_num m)
                  ==>
                  (let o3 = m + (&1:int) in
                   (((&0:int) <= r - l /\ r - o3 < r - l) /\
                    (&0:int) <= o3 /\
                    o3 <= r /\
                    r <= (&(LENGTH a3):int)) /\
                   (!a4:int list.
                      LENGTH a4 = LENGTH a3
                      ==>
                      quicksort_sorted_sub a4 o3 r /\
                      quicksort_permut_sub_prime
                        a3 a4
                        (quicksort_to_num o3)
                        (quicksort_to_num r)
                      ==>
                      quicksort_sorted_sub a4 l r /\
                      quicksort_permut_sub_prime
                        a a4
                        (quicksort_to_num l)
                        (quicksort_to_num r)))))))) /\
       (o1 + (&1:int) < o2
        ==>
        ((&0:int) <= l /\ l < (&(LENGTH a):int)) /\
        (!a1:int list.
           LENGTH a1 = LENGTH a
           ==>
           quicksort_exchange a a1 l l
           ==>
           (((&0:int) <= r - l /\ l - l < r - l) /\
            (&0:int) <= l /\
            l <= l /\
            l <= (&(LENGTH a1):int)) /\
           (!a2:int list.
              LENGTH a2 = LENGTH a1
              ==>
              quicksort_sorted_sub a2 l l /\
              quicksort_permut_sub_prime
                a1 a2
                (quicksort_to_num l)
                (quicksort_to_num l)
              ==>
              (let o3 = l + (&1:int) in
               (((&0:int) <= r - l /\ r - o3 < r - l) /\
                (&0:int) <= o3 /\
                o3 <= r /\
                r <= (&(LENGTH a2):int)) /\
               (!a3:int list.
                  LENGTH a3 = LENGTH a2
                  ==>
                  quicksort_sorted_sub a3 o3 r /\
                  quicksort_permut_sub_prime
                    a2 a3
                    (quicksort_to_num o3)
                    (quicksort_to_num r)
                  ==>
                  quicksort_sorted_sub a3 l r /\
                  quicksort_permut_sub_prime
                    a a3
                    (quicksort_to_num l)
                    (quicksort_to_num r)))))))
    else
      quicksort_sorted_sub a l r /\
      quicksort_permut_sub_prime
        a a (quicksort_to_num l) (quicksort_to_num r)`;;
