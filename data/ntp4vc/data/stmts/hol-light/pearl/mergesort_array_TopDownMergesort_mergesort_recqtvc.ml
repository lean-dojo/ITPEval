(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_TopDownMergesort_mergesort_recqtvc:
  the top-down array mergesort recursion verification condition, including
  total-preorder assumptions, truncating midpoint division, sorted subranges,
  subrange permutations, recursive progress, and merge continuation.
  This file contains no proof.
*)

let mergesort_rec_to_num = new_definition
 `mergesort_rec_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let mergesort_rec_nth = new_definition
 `mergesort_rec_nth (default:A) (a:A list) (i:int) =
    if mergesort_rec_to_num i < LENGTH a
    then EL (mergesort_rec_to_num i) a
    else default`;;

let mergesort_rec_cdiv = new_definition
 `mergesort_rec_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let mergesort_rec_permut_sub = new_definition
 `mergesort_rec_permut_sub
    (a1:A list) (a2:A list) (l:num) (u:num) <=>
    LENGTH a1 = LENGTH a2 /\
    l <= LENGTH a1 /\
    u <= LENGTH a1 /\
    (!v:A.
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a2 /\ EL k a2 = v})`;;

let mergesort_rec_permut_sub_prime = new_definition
 `mergesort_rec_permut_sub_prime
    (a1:A list) (a2:A list) (l:num) (u:num) <=>
    LENGTH a1 = LENGTH a2 /\
    (!k:num.
       k < l /\ k < LENGTH a1
       ==>
       EL k a1 = EL k a2) /\
    (!k:num.
       u <= k /\ k < LENGTH a1
       ==>
       EL k a1 = EL k a2) /\
    (!v:A.
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a2 /\ EL k a2 = v})`;;

let mergesort_rec_sorted_sub = new_definition
 `mergesort_rec_sorted_sub
    (default:A) (le:A->A->bool) (a:A list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 < i2 /\ i2 < u
      ==>
      le (mergesort_rec_nth default a i1)
         (mergesort_rec_nth default a i2)`;;

let statement =
 `!default:A.
  !le:A->A->bool.
  !l r:int.
  !(a:A list) (tmp:A list).
    (!x:A. le x x) /\
    (!x y z:A. le x y /\ le y z ==> le x z) /\
    (!x y:A. le x y \/ le y x)
    ==>
    (&0:int) <= l
    ==>
    l <= r
    ==>
    r <= (&(LENGTH a):int)
    ==>
    LENGTH a = LENGTH tmp
    ==>
    if r - (&1:int) <= l then
      mergesort_rec_sorted_sub default le a l r /\
      mergesort_rec_permut_sub_prime
        a a (mergesort_rec_to_num l) (mergesort_rec_to_num r)
    else
      ~((&2:int) = (&0:int)) /\
      (let m =
         l + mergesort_rec_cdiv (r - l) (&2:int) in
       (((&0:int) <= r - l /\ m - l < r - l) /\
        (&0:int) <= l /\
        l <= m /\
        m <= (&(LENGTH a):int) /\
        LENGTH a = LENGTH tmp) /\
       (!(tmp1:A list) (a1:A list).
          LENGTH tmp1 = LENGTH tmp
          ==>
          LENGTH a1 = LENGTH a
          ==>
          mergesort_rec_sorted_sub default le a1 l m /\
          mergesort_rec_permut_sub_prime
            a a1 (mergesort_rec_to_num l) (mergesort_rec_to_num m)
          ==>
          (((&0:int) <= r - l /\ r - m < r - l) /\
           (&0:int) <= m /\
           m <= r /\
           r <= (&(LENGTH a1):int) /\
           LENGTH a1 = LENGTH tmp1) /\
          (!(tmp2:A list) (a2:A list).
             LENGTH tmp2 = LENGTH tmp1
             ==>
             LENGTH a2 = LENGTH a1
             ==>
             mergesort_rec_sorted_sub default le a2 m r /\
             mergesort_rec_permut_sub_prime
               a1 a2 (mergesort_rec_to_num m) (mergesort_rec_to_num r)
             ==>
             (((&0:int) <= l /\
               l <= m /\
               m <= r /\
               r <= (&(LENGTH tmp2):int) /\
               LENGTH tmp2 = LENGTH a2) /\
              mergesort_rec_sorted_sub default le a2 l m /\
              mergesort_rec_sorted_sub default le a2 m r) /\
             (!a3:A list.
                LENGTH a3 = LENGTH a2
                ==>
                mergesort_rec_sorted_sub default le a3 l r /\
                mergesort_rec_permut_sub
                  a2 a3
                  (mergesort_rec_to_num l)
                  (mergesort_rec_to_num r) /\
                (!i:int.
                   (((&0:int) <= i /\ i < l) \/
                    (r <= i /\ i < (&(LENGTH a3):int)))
                   ==>
                   mergesort_rec_nth default a3 i =
                   mergesort_rec_nth default a2 i)
                ==>
                mergesort_rec_sorted_sub default le a3 l r /\
                mergesort_rec_permut_sub_prime
                  a a3
                  (mergesort_rec_to_num l)
                  (mergesort_rec_to_num r)))))`;;
