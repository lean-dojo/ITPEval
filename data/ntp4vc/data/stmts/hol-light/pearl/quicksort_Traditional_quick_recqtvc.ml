(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/quicksort_Traditional_quick_recqtvc: the traditional quicksort
  recursive verification condition, including bidirectional partition scans,
  swaps, recursive sorted subranges, and subarray permutations. This file
  contains no proof.
*)

let quick_rec_to_num = new_definition
 `quick_rec_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let quick_rec_nth = new_definition
 `quick_rec_nth (a:int list) (i:int) =
    if quick_rec_to_num i < LENGTH a
    then EL (quick_rec_to_num i) a
    else (&0:int)`;;

let quick_rec_update =
  new_recursive_definition list_RECURSION
   `(!n:num. !x:int. quick_rec_update [] n x = []) /\
    (!h:int. !t:int list. !n:num. !x:int.
       quick_rec_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (quick_rec_update t (PRE n) x))`;;

let quick_rec_permut_sub_prime = new_definition
 `quick_rec_permut_sub_prime
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

let quick_rec_array_exchange = new_definition
 `quick_rec_array_exchange
    (old:int list) (new:int list) (i:int) (j:int) <=>
    new =
      quick_rec_update
        (quick_rec_update
          old (quick_rec_to_num i) (quick_rec_nth old j))
        (quick_rec_to_num j)
        (quick_rec_nth old i)`;;

let quick_rec_sorted_sub = new_definition
 `quick_rec_sorted_sub (a:int list) (l:int) (u:int) <=>
    !i1 i2:int.
      l <= i1 /\ i1 <= i2 /\ i2 < u
      ==> quick_rec_nth a i1 <= quick_rec_nth a i2`;;

let quick_rec_all_le_closed = new_definition
 `quick_rec_all_le_closed
    (a:int list) (l:int) (u:int) (v:int) <=>
    !k:int.
      l <= k /\ k <= u
      ==> quick_rec_nth a k <= v`;;

let quick_rec_all_le_half_open = new_definition
 `quick_rec_all_le_half_open
    (a:int list) (l:int) (u:int) (v:int) <=>
    !k:int.
      l <= k /\ k < u
      ==> quick_rec_nth a k <= v`;;

let quick_rec_all_ge_half_open = new_definition
 `quick_rec_all_ge_half_open
    (a:int list) (l:int) (u:int) (v:int) <=>
    !k:int.
      l <= k /\ k < u
      ==> v <= quick_rec_nth a k`;;

let quick_rec_all_ge_open = new_definition
 `quick_rec_all_ge_open
    (a:int list) (l:int) (u:int) (v:int) <=>
    !k:int.
      l < k /\ k < u
      ==> v <= quick_rec_nth a k`;;

let quick_rec_loop_invariant = new_definition
 `quick_rec_loop_invariant
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int) (v:int) <=>
    (l <= i /\ i < r - (&1:int)) /\
    quick_rec_all_le_closed current l i v /\
    (l < j /\ j <= r) /\
    quick_rec_all_ge_half_open current j r v /\
    quick_rec_permut_sub_prime
      original current (quick_rec_to_num l) (quick_rec_to_num r) /\
    quick_rec_nth current l = v`;;

let quick_rec_after_right_recursion = new_definition
 `quick_rec_after_right_recursion
    (original:int list) (after_left:int list)
    (l:int) (right_l:int) (r:int) <=>
    !after_right:int list.
      LENGTH after_right = LENGTH after_left
      ==>
      quick_rec_sorted_sub after_right right_l r /\
      quick_rec_permut_sub_prime
        after_left after_right
        (quick_rec_to_num right_l) (quick_rec_to_num r)
      ==>
      quick_rec_sorted_sub after_right l r /\
      quick_rec_permut_sub_prime
        original after_right (quick_rec_to_num l) (quick_rec_to_num r)`;;

let quick_rec_after_left_recursion = new_definition
 `quick_rec_after_left_recursion
    (original:int list) (after_swap:int list)
    (l:int) (middle:int) (r:int) <=>
    !after_left:int list.
      LENGTH after_left = LENGTH after_swap
      ==>
      quick_rec_sorted_sub after_left l middle /\
      quick_rec_permut_sub_prime
        after_swap after_left
        (quick_rec_to_num l) (quick_rec_to_num middle)
      ==>
      let right_l = middle + (&1:int) in
      ((&0:int) <= r - l /\ r - right_l < r - l) /\
      (&0:int) <= right_l /\
      right_l <= r /\
      r <= (&(LENGTH after_left):int) /\
      quick_rec_after_right_recursion
        original after_left l right_l r`;;

let quick_rec_finish_swap_continuation = new_definition
 `quick_rec_finish_swap_continuation
    (original:int list) (current:int list)
    (l:int) (r:int) (j1:int) <=>
    !after_swap:int list.
      LENGTH after_swap = LENGTH current
      ==>
      quick_rec_array_exchange current after_swap l j1
      ==>
      ((&0:int) <= r - l /\ j1 - l < r - l) /\
      (&0:int) <= l /\
      l <= j1 /\
      j1 <= (&(LENGTH after_swap):int) /\
      quick_rec_after_left_recursion
        original after_swap l j1 r`;;

let quick_rec_finish_result = new_definition
 `quick_rec_finish_result
    (original:int list) (current:int list)
    (l:int) (r:int) (j1:int) <=>
    ((&0:int) <= l /\ l < (&(LENGTH current):int)) /\
    ((&0:int) <= j1 /\ j1 < (&(LENGTH current):int)) /\
    quick_rec_finish_swap_continuation original current l r j1`;;

let quick_rec_loop_swap_continuation = new_definition
 `quick_rec_loop_swap_continuation
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int)
    (i1:int) (j1:int) (v:int) <=>
    !after_swap:int list.
      LENGTH after_swap = LENGTH current
      ==>
      quick_rec_array_exchange current after_swap i1 j1
      ==>
      ((&0:int) <= j - i /\ j1 - i1 < j - i) /\
      (l <= i1 /\ i1 < r - (&1:int)) /\
      quick_rec_all_le_closed after_swap l i1 v /\
      (l < j1 /\ j1 <= r) /\
      quick_rec_all_ge_half_open after_swap j1 r v /\
      quick_rec_permut_sub_prime
        original after_swap (quick_rec_to_num l) (quick_rec_to_num r) /\
      quick_rec_nth after_swap l = v`;;

let quick_rec_loop_swap_result = new_definition
 `quick_rec_loop_swap_result
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int)
    (i1:int) (j1:int) (v:int) <=>
    ((&0:int) <= i1 /\ i1 < (&(LENGTH current):int)) /\
    ((&0:int) <= j1 /\ j1 < (&(LENGTH current):int)) /\
    quick_rec_loop_swap_continuation
      original current l r j i i1 j1 v`;;

let quick_rec_j_progress = new_definition
 `quick_rec_j_progress
    (current:int list) (l:int) (r:int)
    (j:int) (j1:int) (v:int) <=>
    ((&0:int) <= j1 /\ j1 - (&1:int) < j1) /\
    (l <= j1 - (&1:int) /\ j1 - (&1:int) < j) /\
    quick_rec_all_ge_open current (j1 - (&1:int)) r v`;;

let quick_rec_j1_result = new_definition
 `quick_rec_j1_result
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int)
    (i1:int) (j1:int) (v:int) <=>
    ((&0:int) <= j1 /\ j1 < (&(LENGTH current):int)) /\
    if v < quick_rec_nth current j1 then
      if j1 = l then
        if j1 <= i1 then
          quick_rec_finish_result original current l r j1
        else
          quick_rec_loop_swap_result
            original current l r j i i1 j1 v
      else
        quick_rec_j_progress current l r j j1 v
    else
      if j1 <= i1 then
        quick_rec_finish_result original current l r j1
      else
        quick_rec_loop_swap_result
          original current l r j i i1 j1 v`;;

let quick_rec_all_j1 = new_definition
 `quick_rec_all_j1
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int) (i1:int) (v:int) <=>
    !j1:int.
      (l <= j1 /\ j1 < j) /\
      quick_rec_all_ge_open current j1 r v
      ==>
      quick_rec_j1_result original current l r j i i1 j1 v`;;

let quick_rec_j_scan = new_definition
 `quick_rec_j_scan
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int) (i1:int) (v:int) <=>
    (l <= j - (&1:int) /\ j - (&1:int) < j) /\
    quick_rec_all_ge_open current (j - (&1:int)) r v /\
    quick_rec_all_j1 original current l r j i i1 v`;;

let quick_rec_i_progress = new_definition
 `quick_rec_i_progress
    (current:int list) (l:int) (r:int)
    (i:int) (i1:int) (v:int) <=>
    ((&0:int) <= r - i1 /\ r - (i1 + (&1:int)) < r - i1) /\
    (i < i1 + (&1:int) /\ i1 + (&1:int) < r) /\
    quick_rec_all_le_half_open current l (i1 + (&1:int)) v`;;

let quick_rec_i1_result = new_definition
 `quick_rec_i1_result
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int) (i1:int) (v:int) <=>
    ((&0:int) <= i1 /\ i1 < (&(LENGTH current):int)) /\
    if quick_rec_nth current i1 < v then
      if i1 = r - (&1:int) then
        quick_rec_j_scan original current l r j i i1 v
      else
        quick_rec_i_progress current l r i i1 v
    else
      quick_rec_j_scan original current l r j i i1 v`;;

let quick_rec_all_i1 = new_definition
 `quick_rec_all_i1
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int) (v:int) <=>
    !i1:int.
      (i < i1 /\ i1 < r) /\
      quick_rec_all_le_half_open current l i1 v
      ==>
      quick_rec_i1_result original current l r j i i1 v`;;

let quick_rec_loop_state_result = new_definition
 `quick_rec_loop_state_result
    (original:int list) (current:int list)
    (l:int) (r:int) (j:int) (i:int) (v:int) <=>
    (i < i + (&1:int) /\ i + (&1:int) < r) /\
    quick_rec_all_le_half_open current l (i + (&1:int)) v /\
    quick_rec_all_i1 original current l r j i v`;;

let quick_rec_all_loop_states = new_definition
 `quick_rec_all_loop_states
    (original:int list) (l:int) (r:int) (v:int) <=>
    !j i:int. !current:int list.
      LENGTH current = LENGTH original
      ==>
      quick_rec_loop_invariant original current l r j i v
      ==>
      quick_rec_loop_state_result original current l r j i v`;;

let quick_rec_recursive_branch = new_definition
 `quick_rec_recursive_branch (a:int list) (l:int) (r:int) <=>
    (&0:int) <= l /\
    l < (&(LENGTH a):int) /\
    let v = quick_rec_nth a l in
    quick_rec_loop_invariant a a l r r l v /\
    quick_rec_all_loop_states a l r v`;;

let statement =
 `!l r:int. !a:int list.
    (&0:int) <= l
    ==>
    l <= r
    ==>
    r <= (&(LENGTH a):int)
    ==>
    if r <= l + (&1:int) then
      quick_rec_sorted_sub a l r /\
      quick_rec_permut_sub_prime
        a a (quick_rec_to_num l) (quick_rec_to_num r)
    else
      quick_rec_recursive_branch a l r`;;
