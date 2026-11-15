(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_updateqtvc: the cumulative range-sum tree
  point-update verification condition, preserving its interval bounds and
  establishing the updated cell, frame condition, and whole-tree invariant.
  This file contains no proof.
*)

let ntp4vc_sumrange_u_indexes_INDUCT,
    ntp4vc_sumrange_u_indexes_RECURSION =
  define_type
    "ntp4vc_sumrange_u_indexes =
       NTP4VCSumrangeUIndexes int int int";;

let ntp4vc_sumrange_u_low =
  new_recursive_definition ntp4vc_sumrange_u_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_u_low
        (NTP4VCSumrangeUIndexes lo hi s) = lo`;;

let ntp4vc_sumrange_u_high =
  new_recursive_definition ntp4vc_sumrange_u_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_u_high
        (NTP4VCSumrangeUIndexes lo hi s) = hi`;;

let ntp4vc_sumrange_u_isum =
  new_recursive_definition ntp4vc_sumrange_u_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_u_isum
        (NTP4VCSumrangeUIndexes lo hi s) = s`;;

let ntp4vc_sumrange_u_tree_INDUCT,
    ntp4vc_sumrange_u_tree_RECURSION =
  define_type
    "ntp4vc_sumrange_u_tree =
       NTP4VCSumrangeULeaf ntp4vc_sumrange_u_indexes
     | NTP4VCSumrangeUNode
         ntp4vc_sumrange_u_indexes
         ntp4vc_sumrange_u_tree
         ntp4vc_sumrange_u_tree";;

let ntp4vc_sumrange_u_indexes_of =
  new_recursive_definition ntp4vc_sumrange_u_tree_RECURSION
   `(!ind.
       ntp4vc_sumrange_u_indexes_of
         (NTP4VCSumrangeULeaf ind) = ind) /\
    (!ind l r.
       ntp4vc_sumrange_u_indexes_of
         (NTP4VCSumrangeUNode ind l r) = ind)`;;

let ntp4vc_sumrange_u_to_num = new_definition
 `ntp4vc_sumrange_u_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sumrange_u_nth = new_definition
 `ntp4vc_sumrange_u_nth (a:int list) (i:int) =
    if i < (&0:int) then (&0:int)
    else if num_of_int i < LENGTH a
    then EL (num_of_int i) a
    else (&0:int)`;;

let ntp4vc_sumrange_u_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:int. ntp4vc_sumrange_u_update_nat [] n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       ntp4vc_sumrange_u_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h
         (ntp4vc_sumrange_u_update_nat t (PRE n) x))`;;

let ntp4vc_sumrange_u_update = new_definition
 `ntp4vc_sumrange_u_update (a:int list) (i:int) (x:int) =
    ntp4vc_sumrange_u_update_nat a
      (ntp4vc_sumrange_u_to_num i) x`;;

let ntp4vc_sumrange_u_sum_nat =
  new_recursive_definition num_RECURSION
   `(!a:int list. !lower:int.
       ntp4vc_sumrange_u_sum_nat a lower 0 = (&0:int)) /\
    (!a:int list. !lower:int. !n:num.
       ntp4vc_sumrange_u_sum_nat a lower (SUC n) =
       ntp4vc_sumrange_u_nth a lower +
       ntp4vc_sumrange_u_sum_nat
         a (lower + (&1:int)) n)`;;

let ntp4vc_sumrange_u_sum = new_definition
 `ntp4vc_sumrange_u_sum
    (a:int list) (lower:int) (upper:int) =
    ntp4vc_sumrange_u_sum_nat a lower
      (ntp4vc_sumrange_u_to_num (upper - lower))`;;

let ntp4vc_sumrange_u_cdiv = new_definition
 `ntp4vc_sumrange_u_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let ntp4vc_sumrange_u_is_indexes_for = new_definition
 `ntp4vc_sumrange_u_is_indexes_for
    (ind:ntp4vc_sumrange_u_indexes)
    (a:int list) (i:int) (j:int) <=>
    ntp4vc_sumrange_u_low ind = i /\
    ntp4vc_sumrange_u_high ind = j /\
    (&0:int) <= i /\ i < j /\ j <= (&(LENGTH a):int) /\
    ntp4vc_sumrange_u_isum ind =
      ntp4vc_sumrange_u_sum a i j`;;

let ntp4vc_sumrange_u_is_tree_for =
  new_recursive_definition ntp4vc_sumrange_u_tree_RECURSION
   `(!ind a i j.
       ntp4vc_sumrange_u_is_tree_for
         (NTP4VCSumrangeULeaf ind)
         (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_u_is_indexes_for ind a i j /\
        j = i + (&1:int))) /\
    (!ind l r a i j.
       ntp4vc_sumrange_u_is_tree_for
         (NTP4VCSumrangeUNode ind l r)
         (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_u_is_indexes_for ind a i j /\
        i = ntp4vc_sumrange_u_low
              (ntp4vc_sumrange_u_indexes_of l) /\
        j = ntp4vc_sumrange_u_high
              (ntp4vc_sumrange_u_indexes_of r) /\
        (let m =
           ntp4vc_sumrange_u_high
             (ntp4vc_sumrange_u_indexes_of l) in
         m = ntp4vc_sumrange_u_low
               (ntp4vc_sumrange_u_indexes_of r) /\
         i < m /\ m < j /\
         m = ntp4vc_sumrange_u_cdiv (i + j) (&2:int) /\
         ntp4vc_sumrange_u_is_tree_for l a i m /\
         ntp4vc_sumrange_u_is_tree_for r a m j)))`;;

let statement =
 `!i:int.
  !a:int list.
  !t:ntp4vc_sumrange_u_tree.
  !v:int.
    (&0:int) <= i
    ==>
    i < (&(LENGTH a):int)
    ==>
    ntp4vc_sumrange_u_is_tree_for
      t a (&0:int) (&(LENGTH a):int)
    ==>
    ntp4vc_sumrange_u_is_tree_for
      t a
      (ntp4vc_sumrange_u_low
        (ntp4vc_sumrange_u_indexes_of t))
      (ntp4vc_sumrange_u_high
        (ntp4vc_sumrange_u_indexes_of t)) /\
    ntp4vc_sumrange_u_low
      (ntp4vc_sumrange_u_indexes_of t) <= i /\
    i < ntp4vc_sumrange_u_high
          (ntp4vc_sumrange_u_indexes_of t) /\
    (!t1:ntp4vc_sumrange_u_tree.
       ntp4vc_sumrange_u_low
         (ntp4vc_sumrange_u_indexes_of t1) =
         ntp4vc_sumrange_u_low
           (ntp4vc_sumrange_u_indexes_of t) /\
       ntp4vc_sumrange_u_high
         (ntp4vc_sumrange_u_indexes_of t1) =
         ntp4vc_sumrange_u_high
           (ntp4vc_sumrange_u_indexes_of t) /\
       ntp4vc_sumrange_u_is_tree_for
         t1 (ntp4vc_sumrange_u_update a i v)
         (ntp4vc_sumrange_u_low
           (ntp4vc_sumrange_u_indexes_of t1))
         (ntp4vc_sumrange_u_high
           (ntp4vc_sumrange_u_indexes_of t1))
       ==>
       ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
       (LENGTH (ntp4vc_sumrange_u_update a i v) = LENGTH a
        ==>
        (\k:int.
           ntp4vc_sumrange_u_nth
             (ntp4vc_sumrange_u_update a i v) k) =
        (\k:int.
           if k = i then v else ntp4vc_sumrange_u_nth a k)
        ==>
        ntp4vc_sumrange_u_nth
          (ntp4vc_sumrange_u_update a i v) i = v /\
        (!k:int.
           (((&0:int) <= k /\
             k <
               (&(LENGTH
                 (ntp4vc_sumrange_u_update a i v)):int)) /\
            ~(k = i))
           ==>
           ntp4vc_sumrange_u_nth
             (ntp4vc_sumrange_u_update a i v) k =
           ntp4vc_sumrange_u_nth a k) /\
        ntp4vc_sumrange_u_is_tree_for
          t1 (ntp4vc_sumrange_u_update a i v)
          (&0:int)
          (&(LENGTH
            (ntp4vc_sumrange_u_update a i v)):int)))`;;
