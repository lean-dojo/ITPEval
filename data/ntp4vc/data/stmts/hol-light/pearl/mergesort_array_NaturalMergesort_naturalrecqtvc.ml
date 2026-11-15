(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_array_NaturalMergesort_naturalrecqtvc:
  the natural-mergesort recursion verification condition, including scan
  boundaries, sorted subranges, subrange permutations, nested loop
  invariants, and merge continuations. This file contains no proof.
*)

let naturalrec_to_num = new_definition
 `naturalrec_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let naturalrec_nth = new_definition
 `naturalrec_nth (default:A) (a:A list) (i:int) =
    if naturalrec_to_num i < LENGTH a
    then EL (naturalrec_to_num i) a
    else default`;;

let naturalrec_permut_sub = new_definition
 `naturalrec_permut_sub
    (a1:A list) (a2:A list) (l:num) (u:num) <=>
    LENGTH a1 = LENGTH a2 /\
    l <= LENGTH a1 /\
    u <= LENGTH a1 /\
    (!v:A.
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a1 /\ EL k a1 = v} =
       CARD {k:num |
               l <= k /\ k < u /\ k < LENGTH a2 /\ EL k a2 = v})`;;

let naturalrec_permut_sub_prime = new_definition
 `naturalrec_permut_sub_prime
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

let naturalrec_sorted_sub = new_definition
 `naturalrec_sorted_sub
    (default:A) (le:A->A->bool) (a:A list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 < i2 /\ i2 < u
      ==>
      le (naturalrec_nth default a i1)
         (naturalrec_nth default a i2)`;;

let naturalrec_sorted = new_definition
 `naturalrec_sorted
    (default:A) (le:A->A->bool) (a:A list) <=>
    !i1 i2:int.
      (&0:int) <= i1 /\ i1 < i2 /\ i2 < (&(LENGTH a):int)
      ==>
      le (naturalrec_nth default a i1)
         (naturalrec_nth default a i2)`;;

let naturalrec_prefix_eq = new_definition
 `naturalrec_prefix_eq
    (default:A) (a1:A list) (a2:A list) (l:int) <=>
    !j:int.
      (&0:int) <= j /\ j < l
      ==>
      naturalrec_nth default a2 j =
      naturalrec_nth default a1 j`;;

let naturalrec_outside_eq = new_definition
 `naturalrec_outside_eq
    (default:A) (a2:A list) (a3:A list) (lo:int) (hi:int) <=>
    !i:int.
      (((&0:int) <= i /\ i < lo) \/
       (hi <= i /\ i < (&(LENGTH a3):int)))
      ==>
      naturalrec_nth default a3 i =
      naturalrec_nth default a2 i`;;

let naturalrec_final_state = new_definition
 `naturalrec_final_state
    (default:A) (le:A->A->bool)
    (a:A list) (a1:A list) (lo:int) (k:int) (n:int) <=>
    (n = (&(LENGTH a1):int) \/
     lo + k < n /\ n < (&(LENGTH a1):int)) /\
    naturalrec_sorted_sub default le a1 lo n /\
    naturalrec_permut_sub_prime
      a a1 (naturalrec_to_num lo) (LENGTH a1)`;;

let naturalrec_after_merge = new_definition
 `naturalrec_after_merge
    (default:A) (le:A->A->bool)
    (a:A list) (a3:A list)
    (lo:int) (k:int) (i:int) (hi:int) (n:int) <=>
    if hi = n then
      naturalrec_final_state default le a a3 lo k n /\
      naturalrec_prefix_eq default a a3 lo
    else
      (lo + (i + (&1:int)) < hi /\ hi < n) /\
      naturalrec_sorted_sub default le a3 lo hi /\
      naturalrec_permut_sub_prime
        a a3 (naturalrec_to_num lo) (LENGTH a3) /\
      naturalrec_prefix_eq default a a3 lo`;;

let naturalrec_merge_continuation = new_definition
 `naturalrec_merge_continuation
    (default:A) (le:A->A->bool)
    (a:A list) (a2:A list)
    (lo:int) (k:int) (i:int) (hi:int) (n:int) <=>
    !a3:A list.
      LENGTH a3 = LENGTH a2
      ==>
      naturalrec_sorted_sub default le a3 lo hi /\
      naturalrec_permut_sub
        a2 a3 (naturalrec_to_num lo) (naturalrec_to_num hi) /\
      naturalrec_outside_eq default a2 a3 lo hi
      ==>
      naturalrec_after_merge default le a a3 lo k i hi n`;;

let naturalrec_hi_obligation = new_definition
 `naturalrec_hi_obligation
    (default:A) (le:A->A->bool)
    (a:A list) (a1:A list) (a2:A list) (tmp2:A list)
    (lo:int) (k:int) (i:int) (mid:int) (n:int) <=>
    !hi:int.
      (hi = (&(LENGTH a2):int) \/
       mid + i < hi /\ hi < (&(LENGTH a2):int)) /\
      naturalrec_sorted_sub default le a2 mid hi /\
      naturalrec_permut_sub_prime
        a1 a2 (naturalrec_to_num mid) (LENGTH a2) /\
      naturalrec_prefix_eq default a1 a2 mid
      ==>
      (((&0:int) <= lo /\
        lo <= mid /\
        mid <= hi /\
        hi <= (&(LENGTH tmp2):int) /\
        LENGTH tmp2 = LENGTH a2) /\
       naturalrec_sorted_sub default le a2 lo mid /\
       naturalrec_sorted_sub default le a2 mid hi) /\
      naturalrec_merge_continuation
        default le a a2 lo k i hi n`;;

let naturalrec_i_result = new_definition
 `naturalrec_i_result
    (default:A) (le:A->A->bool)
    (a:A list) (a1:A list) (tmp1:A list)
    (lo:int) (k:int) (i:int) (mid:int) (n:int) <=>
    ((&0:int) <= k /\ i < k) /\
    ((&0:int) <= mid /\
     mid <= (&(LENGTH a1):int) /\
     LENGTH a1 = LENGTH tmp1) /\
    (&0:int) <= i /\
    (!a2 tmp2:A list.
       LENGTH a2 = LENGTH a1
       ==>
       LENGTH tmp2 = LENGTH tmp1
       ==>
       naturalrec_hi_obligation
         default le a a1 a2 tmp2 lo k i mid n)`;;

let naturalrec_i_obligation = new_definition
 `naturalrec_i_obligation
    (default:A) (le:A->A->bool)
    (a:A list) (a1:A list) (tmp1:A list)
    (lo:int) (k:int) (o2:int) (mid:int) (n:int) <=>
    !i:int.
      ((&0:int) <= i /\ i <= o2) /\
      (lo + i < mid /\ mid < n) /\
      naturalrec_sorted_sub default le a1 lo mid /\
      naturalrec_permut_sub_prime
        a a1 (naturalrec_to_num lo) (LENGTH a1) /\
      naturalrec_prefix_eq default a a1 lo
      ==>
      naturalrec_i_result
        default le a a1 tmp1 lo k i mid n`;;

let naturalrec_mid_obligation = new_definition
 `naturalrec_mid_obligation
    (default:A) (le:A->A->bool)
    (a:A list) (tmp:A list)
    (lo:int) (k:int) (o2:int) (n:int) <=>
    !mid:int. !a1 tmp1:A list.
      LENGTH a1 = LENGTH a
      ==>
      LENGTH tmp1 = LENGTH tmp
      ==>
      naturalrec_i_obligation
        default le a a1 tmp1 lo k o2 mid n /\
      ((lo + (o2 + (&1:int)) < mid /\ mid < n) /\
       naturalrec_sorted_sub default le a1 lo mid /\
       naturalrec_permut_sub_prime
         a a1 (naturalrec_to_num lo) (LENGTH a1) /\
       naturalrec_prefix_eq default a a1 lo
       ==>
       naturalrec_final_state default le a a1 lo k mid /\
       naturalrec_prefix_eq default a a1 lo)`;;

let naturalrec_o1_result = new_definition
 `naturalrec_o1_result
    (default:A) (le:A->A->bool)
    (a:A list) (tmp:A list)
    (lo:int) (k:int) (o1:int) (n:int) <=>
    if o1 = n then
      naturalrec_final_state default le a a lo k n
    else
      let o2 = k - (&1:int) in
      (((&0:int) <= o2 + (&1:int)
        ==>
        ((lo + (&0:int) < o1 /\ o1 < n) /\
         naturalrec_sorted_sub default le a lo o1 /\
         naturalrec_permut_sub_prime
           a a (naturalrec_to_num lo) (LENGTH a)) /\
        naturalrec_mid_obligation
          default le a tmp lo k o2 n) /\
       (o2 + (&1:int) < (&0:int)
        ==>
        naturalrec_final_state default le a a lo k o1))`;;

let naturalrec_o1_obligation = new_definition
 `naturalrec_o1_obligation
    (default:A) (le:A->A->bool)
    (a:A list) (tmp:A list) (lo:int) (k:int) (n:int) <=>
    !o1:int.
      (lo < o1 /\ o1 <= (&(LENGTH a):int)) /\
      naturalrec_sorted_sub default le a lo o1 /\
      (o1 < (&(LENGTH a):int)
       ==>
       ~le
         (naturalrec_nth default a (o1 - (&1:int)))
         (naturalrec_nth default a o1))
      ==>
      naturalrec_o1_result default le a tmp lo k o1 n`;;

let statement =
 `!default:A.
  !le:A->A->bool.
  !lo:int.
  !a tmp:A list.
  !k:int.
    (!x:A. le x x) /\
    (!x y z:A. le x y /\ le y z ==> le x z) /\
    (!x y:A. le x y \/ le y x)
    ==>
    (&0:int) <= lo
    ==>
    lo <= (&(LENGTH a):int)
    ==>
    LENGTH a = LENGTH tmp
    ==>
    (&0:int) <= k
    ==>
    let n = (&(LENGTH a):int) in
    if n - (&1:int) <= lo then
      naturalrec_final_state default le a a lo k n
    else
      ((&0:int) <= lo /\ lo < (&(LENGTH a):int)) /\
      naturalrec_o1_obligation default le a tmp lo k n`;;
