(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_BottomUpMergesort_bottom_up_mergesortqtvc:
  the bottom-up array mergesort verification condition, including total
  preorder assumptions, sorted runs, permutation invariants, merge-loop
  bounds, and termination measures. This file contains no proof.
*)

let mergesort_array_to_num = new_definition
 `mergesort_array_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let mergesort_array_nth = new_definition
 `mergesort_array_nth (default:A) (a:A list) (i:int) =
    if mergesort_array_to_num i < LENGTH a
    then EL (mergesort_array_to_num i) a
    else default`;;

let mergesort_array_int_min = new_definition
 `mergesort_array_int_min (x:int) (y:int) =
    if x <= y then x else y`;;

let mergesort_array_list_perm = new_definition
 `mergesort_array_list_perm (a1:A list) (a2:A list) <=>
    LENGTH a1 = LENGTH a2 /\
    (!v:A.
       CARD {k:num | k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num | k < LENGTH a2 /\ EL k a2 = v})`;;

let mergesort_array_permut_sub = new_definition
 `mergesort_array_permut_sub
    (a1:A list) (a2:A list) (l:num) (u:num) <=>
    LENGTH a1 = LENGTH a2 /\
    l <= LENGTH a1 /\
    u <= LENGTH a1 /\
    (!v:A.
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a2 /\ EL k a2 = v})`;;

let mergesort_array_sorted_sub = new_definition
 `mergesort_array_sorted_sub
    (default:A) (le:A->A->bool) (a:A list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 < i2 /\ i2 < u
      ==>
      le (mergesort_array_nth default a i1)
         (mergesort_array_nth default a i2)`;;

let mergesort_array_sorted = new_definition
 `mergesort_array_sorted
    (default:A) (le:A->A->bool) (a:A list) <=>
    !i1 i2:int.
      (&0:int) <= i1 /\ i1 < i2 /\ i2 < (&(LENGTH a):int)
      ==>
      le (mergesort_array_nth default a i1)
         (mergesort_array_nth default a i2)`;;

let mergesort_array_runs = new_definition
 `mergesort_array_runs
    (default:A) (le:A->A->bool) (a:A list)
    (n:int) (step:int) (lower:int) (upper:int) <=>
    !k:int.
      let l = k * step in
      lower <= l /\ l < upper
      ==>
      mergesort_array_sorted_sub default le a l
        (mergesort_array_int_min n (l + step))`;;

let mergesort_array_outside_eq = new_definition
 `mergesort_array_outside_eq
    (default:A) (a2:A list) (a3:A list) (lo:int) (hi:int) <=>
    !i:int.
      (((&0:int) <= i /\ i < lo) \/
       (hi <= i /\ i < (&(LENGTH a3):int)))
      ==>
      mergesort_array_nth default a3 i =
      mergesort_array_nth default a2 i`;;

let mergesort_array_merge_continuation = new_definition
 `mergesort_array_merge_continuation
    (default:A) (le:A->A->bool)
    (a1:A list) (a2:A list)
    (n:int) (len:int) (i:int) (mid:int) (hi:int) <=>
    !a3:A list.
      LENGTH a3 = LENGTH a2
      ==>
      (mergesort_array_sorted_sub default le a3
         ((&2:int) * i * len) hi /\
       mergesort_array_permut_sub a2 a3
         (mergesort_array_to_num ((&2:int) * i * len))
         (mergesort_array_to_num hi) /\
       mergesort_array_outside_eq default a2 a3
         ((&2:int) * i * len) hi)
      ==>
      ((&0:int) <= n + len - (&2:int) * i * len /\
       n + len - (mid + len) <
       n + len - (&2:int) * i * len) /\
      ((&0:int) <= mid + len /\
       mid + len = (&2:int) * (i + (&1:int)) * len) /\
      mergesort_array_list_perm a1 a3 /\
      mergesort_array_runs default le a3
        n len (mid + len) n /\
      mergesort_array_runs default le a3
        n ((&2:int) * len) (&0:int) (mid + len)`;;

let mergesort_array_inner_obligation = new_definition
 `mergesort_array_inner_obligation
    (default:A) (le:A->A->bool)
    (a:A list) (tmp1:A list) (a1:A list)
    (n:int) (len:int) <=>
    !i:int. !tmp2:A list. !a2:A list.
      LENGTH tmp2 = LENGTH tmp1
      ==>
      LENGTH a2 = LENGTH a1
      ==>
      ((&0:int) <= (&2:int) * i * len /\
       mergesort_array_list_perm a1 a2 /\
       mergesort_array_runs default le a2
         n len ((&2:int) * i * len) n /\
       mergesort_array_runs default le a2
         n ((&2:int) * len) (&0:int) ((&2:int) * i * len))
      ==>
      (((&2:int) * i * len < n - len
        ==>
        let mid = (&2:int) * i * len + len in
        let hi = mergesort_array_int_min n (mid + len) in
        (((&0:int) <= (&2:int) * i * len /\
          (&2:int) * i * len <= mid /\
          mid <= hi /\
          hi <= (&(LENGTH tmp2):int) /\
          LENGTH tmp2 = LENGTH a2) /\
         mergesort_array_sorted_sub default le a2
           ((&2:int) * i * len) mid /\
         mergesort_array_sorted_sub default le a2 mid hi) /\
        mergesort_array_merge_continuation
          default le a1 a2 n len i mid hi) /\
       (~((&2:int) * i * len < n - len)
        ==>
        ((&0:int) <= (&2:int) * n - len /\
         (&2:int) * n - (&2:int) * len <
         (&2:int) * n - len) /\
        (&1:int) <= (&2:int) * len /\
        mergesort_array_list_perm a a2 /\
        mergesort_array_runs default le a2
          n ((&2:int) * len) (&0:int) n))`;;

let mergesort_array_outer_obligation = new_definition
 `mergesort_array_outer_obligation
    (default:A) (le:A->A->bool)
    (a:A list) (tmp1:A list) (a1:A list)
    (n:int) (len:int) <=>
    ((len < n
      ==>
      (((&0:int) <= (&0:int) /\
        (&0:int) = (&2:int) * (&0:int) * len) /\
       mergesort_array_list_perm a1 a1 /\
       mergesort_array_runs default le a1
         n len (&0:int) n /\
       mergesort_array_runs default le a1
         n ((&2:int) * len) (&0:int) (&0:int)) /\
      mergesort_array_inner_obligation
        default le a tmp1 a1 n len) /\
     (~(len < n)
      ==>
      mergesort_array_sorted default le a1 /\
      mergesort_array_list_perm a a1))`;;

let statement =
 `!default:A.
  !le:A->A->bool.
  !a:A list.
    (!x:A. le x x) /\
    (!x y z:A. le x y /\ le y z ==> le x z) /\
    (!x y:A. le x y \/ le y x)
    ==>
    let n = (&(LENGTH a):int) in
    !tmp:A list.
      LENGTH tmp = LENGTH a /\
      (!i:int.
         (&0:int) <= i /\ i < (&(LENGTH tmp):int)
         ==>
         mergesort_array_nth default tmp i =
         mergesort_array_nth default a i)
      ==>
      ((&1:int) <= (&1:int) /\
       mergesort_array_list_perm a a /\
       mergesort_array_runs default le a
         n (&1:int) (&0:int) n) /\
      (!len:int. !tmp1:A list. !a1:A list.
         LENGTH tmp1 = LENGTH tmp
         ==>
         LENGTH a1 = LENGTH a
         ==>
         ((&1:int) <= len /\
          mergesort_array_list_perm a a1 /\
          mergesort_array_runs default le a1
            n len (&0:int) n)
         ==>
         mergesort_array_outer_obligation
           default le a tmp1 a1 n len)`;;
