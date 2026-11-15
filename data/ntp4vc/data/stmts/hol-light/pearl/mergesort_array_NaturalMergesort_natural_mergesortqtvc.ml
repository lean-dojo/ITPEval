(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_NaturalMergesort_natural_mergesortqtvc:
  the natural array mergesort verification condition, including total-preorder
  assumptions, sorted runs, permutation invariants, merge boundaries, and
  termination measures. This file contains no proof.
*)

let natural_mergesort_to_num = new_definition
 `natural_mergesort_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let natural_mergesort_nth = new_definition
 `natural_mergesort_nth (default:A) (a:A list) (i:int) =
    if natural_mergesort_to_num i < LENGTH a
    then EL (natural_mergesort_to_num i) a
    else default`;;

let natural_mergesort_list_perm = new_definition
 `natural_mergesort_list_perm (a1:A list) (a2:A list) <=>
    LENGTH a1 = LENGTH a2 /\
    (!v:A.
       CARD {k:num | k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num | k < LENGTH a2 /\ EL k a2 = v})`;;

let natural_mergesort_permut_sub = new_definition
 `natural_mergesort_permut_sub
    (a1:A list) (a2:A list) (l:num) (u:num) <=>
    LENGTH a1 = LENGTH a2 /\
    l <= LENGTH a1 /\
    u <= LENGTH a1 /\
    (!v:A.
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a2 /\ EL k a2 = v})`;;

let natural_mergesort_sorted_sub = new_definition
 `natural_mergesort_sorted_sub
    (default:A) (le:A->A->bool) (a:A list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 < i2 /\ i2 < u
      ==>
      le (natural_mergesort_nth default a i1)
         (natural_mergesort_nth default a i2)`;;

let natural_mergesort_sorted = new_definition
 `natural_mergesort_sorted
    (default:A) (le:A->A->bool) (a:A list) <=>
    !i1 i2:int.
      (&0:int) <= i1 /\ i1 < i2 /\ i2 < (&(LENGTH a):int)
      ==>
      le (natural_mergesort_nth default a i1)
         (natural_mergesort_nth default a i2)`;;

let natural_mergesort_after_merge = new_definition
 `natural_mergesort_after_merge
    (default:A) (le:A->A->bool)
    (a1:A list) (a3:A list)
    (n:int) (first_run:int) (first_run1:int) (lo:int) (hi:int) <=>
    ((lo = (&0:int)
      ==>
      ((&0:int) <= n - lo /\ n - hi < n - lo) /\
      ((&0:int) <= hi /\ hi <= n) /\
      (first_run <= hi /\ hi <= n) /\
      natural_mergesort_sorted_sub default le a3 (&0:int) hi /\
      (hi = (&0:int) \/ hi <= hi /\ first_run < hi) /\
      natural_mergesort_list_perm a1 a3) /\
     (~(lo = (&0:int))
      ==>
      ((&0:int) <= n - lo /\ n - hi < n - lo) /\
      ((&0:int) <= hi /\ hi <= n) /\
      (first_run <= first_run1 /\ first_run1 <= n) /\
      natural_mergesort_sorted_sub default le a3 (&0:int) first_run1 /\
      (hi = (&0:int) \/
       first_run1 <= hi /\ first_run < first_run1) /\
      natural_mergesort_list_perm a1 a3))`;;

let natural_mergesort_merge_continuation = new_definition
 `natural_mergesort_merge_continuation
    (default:A) (le:A->A->bool)
    (a1:A list) (a2:A list)
    (n:int) (first_run:int) (first_run1:int) (lo:int) (hi:int) <=>
    !a3:A list.
      LENGTH a3 = LENGTH a2
      ==>
      (natural_mergesort_sorted_sub default le a3 lo hi /\
       natural_mergesort_permut_sub a2 a3
         (natural_mergesort_to_num lo)
         (natural_mergesort_to_num hi) /\
       (!i:int.
          (((&0:int) <= i /\ i < lo) \/
           (hi <= i /\ i < (&(LENGTH a3):int)))
          ==>
          natural_mergesort_nth default a3 i =
          natural_mergesort_nth default a2 i))
      ==>
      natural_mergesort_after_merge
        default le a1 a3 n first_run first_run1 lo hi`;;

let natural_mergesort_hi_obligation = new_definition
 `natural_mergesort_hi_obligation
    (default:A) (le:A->A->bool)
    (a1:A list) (tmp2:A list) (a2:A list)
    (n:int) (first_run:int) (first_run1:int) (lo:int) (mid:int) <=>
    !hi:int.
      ((mid < hi /\ hi <= (&(LENGTH a2):int)) /\
       natural_mergesort_sorted_sub default le a2 mid hi /\
       (hi < (&(LENGTH a2):int)
        ==>
        ~le
          (natural_mergesort_nth default a2 (hi - (&1:int)))
          (natural_mergesort_nth default a2 hi)))
      ==>
      (((&0:int) <= lo /\
        lo <= mid /\
        mid <= hi /\
        hi <= (&(LENGTH tmp2):int) /\
        LENGTH tmp2 = LENGTH a2) /\
       natural_mergesort_sorted_sub default le a2 lo mid /\
       natural_mergesort_sorted_sub default le a2 mid hi) /\
      natural_mergesort_merge_continuation
        default le a1 a2 n first_run first_run1 lo hi`;;

let natural_mergesort_mid_result = new_definition
 `natural_mergesort_mid_result
    (default:A) (le:A->A->bool)
    (a:A list) (a1:A list) (tmp2:A list) (a2:A list)
    (n:int) (first_run:int) (first_run1:int) (lo:int) (mid:int) <=>
    ((mid = n
      ==>
      ((lo = (&0:int)
        ==>
        natural_mergesort_sorted default le a2 /\
        natural_mergesort_list_perm a a2) /\
       (~(lo = (&0:int))
        ==>
        ((&0:int) <= n - first_run /\
         n - first_run1 < n - first_run) /\
        (((&0:int) <= first_run1 /\ first_run1 <= n) /\
         natural_mergesort_sorted_sub
           default le a2 (&0:int) first_run1) /\
        natural_mergesort_list_perm a a2))) /\
     (~(mid = n)
      ==>
      ((&0:int) <= mid /\ mid < (&(LENGTH a2):int)) /\
      natural_mergesort_hi_obligation
        default le a1 tmp2 a2 n first_run first_run1 lo mid))`;;

let natural_mergesort_mid_obligation = new_definition
 `natural_mergesort_mid_obligation
    (default:A) (le:A->A->bool)
    (a:A list) (a1:A list) (tmp2:A list) (a2:A list)
    (n:int) (first_run:int) (first_run1:int) (lo:int) <=>
    !mid:int.
      ((lo < mid /\ mid <= (&(LENGTH a2):int)) /\
       natural_mergesort_sorted_sub default le a2 lo mid /\
       (mid < (&(LENGTH a2):int)
        ==>
        ~le
          (natural_mergesort_nth default a2 (mid - (&1:int)))
          (natural_mergesort_nth default a2 mid)))
      ==>
      natural_mergesort_mid_result
        default le a a1 tmp2 a2 n first_run first_run1 lo mid`;;

let natural_mergesort_lo_result = new_definition
 `natural_mergesort_lo_result
    (default:A) (le:A->A->bool)
    (a:A list) (a1:A list) (tmp2:A list) (a2:A list)
    (n:int) (first_run:int) (first_run1:int) (lo:int) <=>
    ((lo < n - (&1:int)
      ==>
      ((&0:int) <= lo /\ lo < (&(LENGTH a2):int)) /\
      natural_mergesort_mid_obligation
        default le a a1 tmp2 a2 n first_run first_run1 lo) /\
     (~(lo < n - (&1:int))
      ==>
      ((&0:int) <= n - first_run /\
       n - first_run1 < n - first_run) /\
      (((&0:int) <= first_run1 /\ first_run1 <= n) /\
       natural_mergesort_sorted_sub
         default le a2 (&0:int) first_run1) /\
      natural_mergesort_list_perm a a2))`;;

let natural_mergesort_first_run_continuation = new_definition
 `natural_mergesort_first_run_continuation
    (default:A) (le:A->A->bool)
    (a:A list) (tmp1:A list) (a1:A list)
    (n:int) (first_run:int) <=>
    !lo first_run1:int. !tmp2 a2:A list.
      LENGTH tmp2 = LENGTH tmp1
      ==>
      LENGTH a2 = LENGTH a1
      ==>
      ((&0:int) <= lo /\ lo <= n) /\
      (first_run <= first_run1 /\ first_run1 <= n) /\
      natural_mergesort_sorted_sub
        default le a2 (&0:int) first_run1 /\
      (lo = (&0:int) \/
       first_run1 <= lo /\ first_run < first_run1) /\
      natural_mergesort_list_perm a1 a2
      ==>
      natural_mergesort_lo_result
        default le a a1 tmp2 a2 n first_run first_run1 lo`;;

let natural_mergesort_outer_obligation = new_definition
 `natural_mergesort_outer_obligation
    (default:A) (le:A->A->bool)
    (a:A list) (tmp:A list) (n:int) <=>
    !first_run:int. !tmp1 a1:A list.
      LENGTH tmp1 = LENGTH tmp
      ==>
      LENGTH a1 = LENGTH a
      ==>
      ((((&0:int) <= first_run /\ first_run <= n) /\
        natural_mergesort_sorted_sub
          default le a1 (&0:int) first_run) /\
       natural_mergesort_list_perm a a1)
      ==>
      (((&0:int) <= (&0:int) /\ (&0:int) <= n) /\
       (first_run <= first_run /\ first_run <= n) /\
       natural_mergesort_sorted_sub default le a1 (&0:int) first_run /\
       natural_mergesort_list_perm a1 a1) /\
      natural_mergesort_first_run_continuation
        default le a tmp1 a1 n first_run`;;

let statement =
 `!default:A.
  !le:A->A->bool.
  !a:A list.
    (!x:A. le x x) /\
    (!x y z:A. le x y /\ le y z ==> le x z) /\
    (!x y:A. le x y \/ le y x)
    ==>
    let n = (&(LENGTH a):int) in
    ((n <= (&1:int)
      ==>
      natural_mergesort_sorted default le a /\
      natural_mergesort_list_perm a a) /\
     (~(n <= (&1:int))
      ==>
      !tmp:A list.
        LENGTH tmp = LENGTH a /\
        (!i:int.
           (&0:int) <= i /\ i < (&(LENGTH tmp):int)
           ==>
           natural_mergesort_nth default tmp i =
           natural_mergesort_nth default a i)
        ==>
        ((((&0:int) <= (&0:int) /\ (&0:int) <= n) /\
          natural_mergesort_sorted_sub
            default le a (&0:int) (&0:int)) /\
         natural_mergesort_list_perm a a) /\
        natural_mergesort_outer_obligation default le a tmp n))`;;
