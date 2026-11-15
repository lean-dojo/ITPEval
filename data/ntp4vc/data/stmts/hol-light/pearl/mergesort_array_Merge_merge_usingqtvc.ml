(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_Merge_merge_usingqtvc: a merge-step verification
  condition for adjacent sorted array segments, including total-preorder
  assumptions, copying through a temporary list, subrange permutation, and
  preservation outside the merged interval. This file contains no proof.
*)

let merge_using_to_num = new_definition
 `merge_using_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let merge_using_nth = new_definition
 `merge_using_nth (default:A) (a:A list) (i:int) =
    if merge_using_to_num i < LENGTH a
    then EL (merge_using_to_num i) a
    else default`;;

let merge_using_permut_sub = new_definition
 `merge_using_permut_sub
    (a1:A list) (a2:A list) (l:num) (u:num) <=>
    LENGTH a1 = LENGTH a2 /\
    l <= LENGTH a1 /\
    u <= LENGTH a1 /\
    (!v:A.
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a2 /\ EL k a2 = v})`;;

let merge_using_sorted_sub = new_definition
 `merge_using_sorted_sub
    (default:A) (le:A->A->bool) (a:A list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 < i2 /\ i2 < u
      ==>
      le (merge_using_nth default a i1)
         (merge_using_nth default a i2)`;;

let statement =
 `!default:A.
  !le:A->A->bool.
  !l m r:int.
  !tmp a:A list.
  !o1:bool.
    (!x:A. le x x) /\
    (!x y z:A. le x y /\ le y z ==> le x z) /\
    (!x y:A. le x y \/ le y x)
    ==>
    (&0:int) <= l
    ==>
    l <= m
    ==>
    m <= r
    ==>
    r <= (&(LENGTH tmp):int)
    ==>
    LENGTH tmp = LENGTH a
    ==>
    merge_using_sorted_sub default le a l m
    ==>
    merge_using_sorted_sub default le a m r
    ==>
    (if l < m
     then o1 = (if m < r then T else F)
     else o1 = F)
    ==>
    if o1 = T then
      ((&0:int) <= m /\ m < (&(LENGTH a):int)) /\
      (let o2 = m - (&1:int) in
       ((&0:int) <= o2 /\ o2 < (&(LENGTH a):int)) /\
       (if le (merge_using_nth default a o2)
              (merge_using_nth default a m)
        then
          merge_using_sorted_sub default le a l r /\
          merge_using_permut_sub a a
            (merge_using_to_num l) (merge_using_to_num r)
        else
          let o3 = r - l in
          (((&0:int) <= l /\
            (&0:int) <= o3 /\
            l + o3 <= (&(LENGTH a):int)) /\
           (&0:int) <= l /\
           l + o3 <= (&(LENGTH tmp):int)) /\
          (!tmp1:A list.
             LENGTH tmp1 = LENGTH tmp
             ==>
             ((!i:int.
                 (((&0:int) <= i /\ i < l) \/
                  (l + o3 <= i /\ i < (&(LENGTH tmp1):int)))
                 ==>
                 merge_using_nth default tmp1 i =
                 merge_using_nth default tmp i) /\
              (!i:int.
                 l <= i /\ i < l + o3
                 ==>
                 merge_using_nth default tmp1 i =
                 merge_using_nth default a (l + i - l)))
             ==>
             (((&0:int) <= l /\
               l <= m /\
               m <= r /\
               r <= (&(LENGTH tmp1):int) /\
               LENGTH tmp1 = LENGTH a) /\
              merge_using_sorted_sub default le tmp1 l m /\
              merge_using_sorted_sub default le tmp1 m r) /\
             (!a1:A list.
                LENGTH a1 = LENGTH a
                ==>
                (merge_using_sorted_sub default le a1 l r /\
                 merge_using_permut_sub tmp1 a1
                   (merge_using_to_num l) (merge_using_to_num r) /\
                 (!i:int.
                    (((&0:int) <= i /\ i < l) \/
                     (r <= i /\ i < (&(LENGTH a1):int)))
                    ==>
                    merge_using_nth default a1 i =
                    merge_using_nth default a i))
                ==>
                merge_using_sorted_sub default le a1 l r /\
                merge_using_permut_sub a a1
                  (merge_using_to_num l) (merge_using_to_num r) /\
                (!i:int.
                   (((&0:int) <= i /\ i < l) \/
                    (r <= i /\ i < (&(LENGTH a1):int)))
                   ==>
                   merge_using_nth default a1 i =
                   merge_using_nth default a i)))))
    else
      merge_using_sorted_sub default le a l r /\
      merge_using_permut_sub a a
        (merge_using_to_num l) (merge_using_to_num r)`;;
