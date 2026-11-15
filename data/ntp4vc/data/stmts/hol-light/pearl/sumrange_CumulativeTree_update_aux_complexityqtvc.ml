(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_update_aux_complexityqtvc: the verification
  condition for a cumulative range-sum tree point update, preserving subtree
  intervals and sums while bounding the recursive update's credit increase by
  the tree depth. This file contains no proof.
*)

let ntp4vc_sumrange_uac_indexes_INDUCT,
    ntp4vc_sumrange_uac_indexes_RECURSION =
  define_type
    "ntp4vc_sumrange_uac_indexes =
       NTP4VCSumrangeUACIndexes int int int";;

let ntp4vc_sumrange_uac_low =
  new_recursive_definition ntp4vc_sumrange_uac_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_uac_low
        (NTP4VCSumrangeUACIndexes lo hi s) = lo`;;

let ntp4vc_sumrange_uac_high =
  new_recursive_definition ntp4vc_sumrange_uac_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_uac_high
        (NTP4VCSumrangeUACIndexes lo hi s) = hi`;;

let ntp4vc_sumrange_uac_isum =
  new_recursive_definition ntp4vc_sumrange_uac_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_uac_isum
        (NTP4VCSumrangeUACIndexes lo hi s) = s`;;

let ntp4vc_sumrange_uac_tree_INDUCT,
    ntp4vc_sumrange_uac_tree_RECURSION =
  define_type
    "ntp4vc_sumrange_uac_tree =
       NTP4VCSumrangeUACLeaf ntp4vc_sumrange_uac_indexes
     | NTP4VCSumrangeUACNode
         ntp4vc_sumrange_uac_indexes
         ntp4vc_sumrange_uac_tree
         ntp4vc_sumrange_uac_tree";;

let ntp4vc_sumrange_uac_indexes_of =
  new_recursive_definition ntp4vc_sumrange_uac_tree_RECURSION
   `(!ind.
       ntp4vc_sumrange_uac_indexes_of
         (NTP4VCSumrangeUACLeaf ind) = ind) /\
    (!ind l r.
       ntp4vc_sumrange_uac_indexes_of
         (NTP4VCSumrangeUACNode ind l r) = ind)`;;

let ntp4vc_sumrange_uac_to_num = new_definition
 `ntp4vc_sumrange_uac_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sumrange_uac_nth = new_definition
 `ntp4vc_sumrange_uac_nth (a:int list) (i:int) =
    if ntp4vc_sumrange_uac_to_num i < LENGTH a
    then EL (ntp4vc_sumrange_uac_to_num i) a
    else (&0:int)`;;

let ntp4vc_sumrange_uac_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:int. ntp4vc_sumrange_uac_update_nat [] n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       ntp4vc_sumrange_uac_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h
         (ntp4vc_sumrange_uac_update_nat t (PRE n) x))`;;

let ntp4vc_sumrange_uac_update = new_definition
 `ntp4vc_sumrange_uac_update (a:int list) (i:int) (x:int) =
    ntp4vc_sumrange_uac_update_nat a
      (ntp4vc_sumrange_uac_to_num i) x`;;

let ntp4vc_sumrange_uac_sum_nat =
  new_recursive_definition num_RECURSION
   `(!a:int list. !lower:int.
       ntp4vc_sumrange_uac_sum_nat a lower 0 = (&0:int)) /\
    (!a:int list. !lower:int. !n:num.
       ntp4vc_sumrange_uac_sum_nat a lower (SUC n) =
       ntp4vc_sumrange_uac_nth a lower +
       ntp4vc_sumrange_uac_sum_nat
         a (lower + (&1:int)) n)`;;

let ntp4vc_sumrange_uac_sum = new_definition
 `ntp4vc_sumrange_uac_sum
    (a:int list) (lower:int) (upper:int) =
    ntp4vc_sumrange_uac_sum_nat a lower
      (ntp4vc_sumrange_uac_to_num (upper - lower))`;;

let ntp4vc_sumrange_uac_cdiv = new_definition
 `ntp4vc_sumrange_uac_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let ntp4vc_sumrange_uac_int_max = new_definition
 `ntp4vc_sumrange_uac_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let ntp4vc_sumrange_uac_is_indexes_for = new_definition
 `ntp4vc_sumrange_uac_is_indexes_for
    (ind:ntp4vc_sumrange_uac_indexes)
    (a:int list) (i:int) (j:int) <=>
    ntp4vc_sumrange_uac_low ind = i /\
    ntp4vc_sumrange_uac_high ind = j /\
    (&0:int) <= i /\ i < j /\ j <= (&(LENGTH a):int) /\
    ntp4vc_sumrange_uac_isum ind =
      ntp4vc_sumrange_uac_sum a i j`;;

let ntp4vc_sumrange_uac_is_tree_for =
  new_recursive_definition ntp4vc_sumrange_uac_tree_RECURSION
   `(!ind a i j.
       ntp4vc_sumrange_uac_is_tree_for
         (NTP4VCSumrangeUACLeaf ind)
         (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_uac_is_indexes_for ind a i j /\
        j = i + (&1:int))) /\
    (!ind l r a i j.
       ntp4vc_sumrange_uac_is_tree_for
         (NTP4VCSumrangeUACNode ind l r)
         (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_uac_is_indexes_for ind a i j /\
        i = ntp4vc_sumrange_uac_low
              (ntp4vc_sumrange_uac_indexes_of l) /\
        j = ntp4vc_sumrange_uac_high
              (ntp4vc_sumrange_uac_indexes_of r) /\
        (let m =
           ntp4vc_sumrange_uac_high
             (ntp4vc_sumrange_uac_indexes_of l) in
         m = ntp4vc_sumrange_uac_low
               (ntp4vc_sumrange_uac_indexes_of r) /\
         i < m /\ m < j /\
         m = ntp4vc_sumrange_uac_cdiv (i + j) (&2:int) /\
         ntp4vc_sumrange_uac_is_tree_for l a i m /\
         ntp4vc_sumrange_uac_is_tree_for r a m j)))`;;

let ntp4vc_sumrange_uac_depth =
  new_recursive_definition ntp4vc_sumrange_uac_tree_RECURSION
   `(!ind.
       ntp4vc_sumrange_uac_depth
         (NTP4VCSumrangeUACLeaf ind) = (&1:int)) /\
    (!ind l r.
       ntp4vc_sumrange_uac_depth
         (NTP4VCSumrangeUACNode ind l r) =
       (&1:int) +
       ntp4vc_sumrange_uac_int_max
         (ntp4vc_sumrange_uac_depth l)
         (ntp4vc_sumrange_uac_depth r))`;;

let ntp4vc_sumrange_uac_is_child =
  new_recursive_definition ntp4vc_sumrange_uac_tree_RECURSION
   `(!child ind.
       ntp4vc_sumrange_uac_is_child
         (child:ntp4vc_sumrange_uac_tree)
         (NTP4VCSumrangeUACLeaf ind) = F) /\
    (!child ind l r.
       ntp4vc_sumrange_uac_is_child
         (child:ntp4vc_sumrange_uac_tree)
         (NTP4VCSumrangeUACNode ind l r) =
       (child = l \/ child = r))`;;

let ntp4vc_sumrange_uac_new_left =
  new_definition
   `ntp4vc_sumrange_uac_new_left ind l' r (a:int list) (i:int) (v:int) =
      NTP4VCSumrangeUACNode
        (NTP4VCSumrangeUACIndexes
          (ntp4vc_sumrange_uac_low ind)
          (ntp4vc_sumrange_uac_high ind)
          (ntp4vc_sumrange_uac_isum ind +
           (v - ntp4vc_sumrange_uac_nth a i)))
        l' r`;;

let ntp4vc_sumrange_uac_new_right =
  new_definition
   `ntp4vc_sumrange_uac_new_right ind l r' (a:int list) (i:int) (v:int) =
      NTP4VCSumrangeUACNode
        (NTP4VCSumrangeUACIndexes
          (ntp4vc_sumrange_uac_low ind)
          (ntp4vc_sumrange_uac_high ind)
          (ntp4vc_sumrange_uac_isum ind +
           (v - ntp4vc_sumrange_uac_nth a i)))
        l r'`;;

let ntp4vc_sumrange_uac_leaf_vc =
  new_definition
   `ntp4vc_sumrange_uac_leaf_vc ind (a:int list) (i:int) (v:int) (c:int) <=>
      c + (&1:int) - c <=
        ntp4vc_sumrange_uac_depth (NTP4VCSumrangeUACLeaf ind) /\
      v - ntp4vc_sumrange_uac_isum ind =
        v - ntp4vc_sumrange_uac_nth a i /\
      ntp4vc_sumrange_uac_low
        (ntp4vc_sumrange_uac_indexes_of
          (NTP4VCSumrangeUACLeaf
            (NTP4VCSumrangeUACIndexes
              (ntp4vc_sumrange_uac_low ind)
              (ntp4vc_sumrange_uac_high ind) v))) =
      ntp4vc_sumrange_uac_low
        (ntp4vc_sumrange_uac_indexes_of
          (NTP4VCSumrangeUACLeaf ind)) /\
      ntp4vc_sumrange_uac_high
        (ntp4vc_sumrange_uac_indexes_of
          (NTP4VCSumrangeUACLeaf
            (NTP4VCSumrangeUACIndexes
              (ntp4vc_sumrange_uac_low ind)
              (ntp4vc_sumrange_uac_high ind) v))) =
      ntp4vc_sumrange_uac_high
        (ntp4vc_sumrange_uac_indexes_of
          (NTP4VCSumrangeUACLeaf ind)) /\
      ntp4vc_sumrange_uac_is_tree_for
        (NTP4VCSumrangeUACLeaf
          (NTP4VCSumrangeUACIndexes
            (ntp4vc_sumrange_uac_low ind)
            (ntp4vc_sumrange_uac_high ind) v))
        (ntp4vc_sumrange_uac_update a i v)
        (ntp4vc_sumrange_uac_low ind)
        (ntp4vc_sumrange_uac_high ind)`;;

let ntp4vc_sumrange_uac_left_pre =
  new_definition
   `ntp4vc_sumrange_uac_left_pre ind l r (a:int list) (i:int) <=>
      ntp4vc_sumrange_uac_is_child l
        (NTP4VCSumrangeUACNode ind l r) /\
      ntp4vc_sumrange_uac_is_tree_for l a
        (ntp4vc_sumrange_uac_low
          (ntp4vc_sumrange_uac_indexes_of l))
        (ntp4vc_sumrange_uac_high
          (ntp4vc_sumrange_uac_indexes_of l)) /\
      ntp4vc_sumrange_uac_low
        (ntp4vc_sumrange_uac_indexes_of l) <= i /\
      i < ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of l)`;;

let ntp4vc_sumrange_uac_right_pre =
  new_definition
   `ntp4vc_sumrange_uac_right_pre ind l r (a:int list) (i:int) <=>
      ntp4vc_sumrange_uac_is_child r
        (NTP4VCSumrangeUACNode ind l r) /\
      ntp4vc_sumrange_uac_is_tree_for r a
        (ntp4vc_sumrange_uac_low
          (ntp4vc_sumrange_uac_indexes_of r))
        (ntp4vc_sumrange_uac_high
          (ntp4vc_sumrange_uac_indexes_of r)) /\
      ntp4vc_sumrange_uac_low
        (ntp4vc_sumrange_uac_indexes_of r) <= i /\
      i < ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of r)`;;

let ntp4vc_sumrange_uac_left_post =
  new_definition
   `ntp4vc_sumrange_uac_left_post ind l r
       (a:int list) (i:int) (v:int) (c:int) <=>
      !c1:int. !l':ntp4vc_sumrange_uac_tree.
        c1 - (c + (&1:int)) <= ntp4vc_sumrange_uac_depth l /\
        ntp4vc_sumrange_uac_low
          (ntp4vc_sumrange_uac_indexes_of l') =
          ntp4vc_sumrange_uac_low
            (ntp4vc_sumrange_uac_indexes_of l) /\
        ntp4vc_sumrange_uac_high
          (ntp4vc_sumrange_uac_indexes_of l') =
          ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of l) /\
        ntp4vc_sumrange_uac_is_tree_for l'
          (ntp4vc_sumrange_uac_update a i v)
          (ntp4vc_sumrange_uac_low
            (ntp4vc_sumrange_uac_indexes_of l'))
          (ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of l'))
        ==>
        c1 - c <=
          ntp4vc_sumrange_uac_depth
            (NTP4VCSumrangeUACNode ind l r) /\
        ntp4vc_sumrange_uac_low
          (ntp4vc_sumrange_uac_indexes_of
            (ntp4vc_sumrange_uac_new_left ind l' r a i v)) =
          ntp4vc_sumrange_uac_low ind /\
        ntp4vc_sumrange_uac_high
          (ntp4vc_sumrange_uac_indexes_of
            (ntp4vc_sumrange_uac_new_left ind l' r a i v)) =
          ntp4vc_sumrange_uac_high ind /\
        ntp4vc_sumrange_uac_is_tree_for
          (ntp4vc_sumrange_uac_new_left ind l' r a i v)
          (ntp4vc_sumrange_uac_update a i v)
          (ntp4vc_sumrange_uac_low
            (ntp4vc_sumrange_uac_indexes_of
              (ntp4vc_sumrange_uac_new_left ind l' r a i v)))
          (ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of
              (ntp4vc_sumrange_uac_new_left ind l' r a i v)))`;;

let ntp4vc_sumrange_uac_right_post =
  new_definition
   `ntp4vc_sumrange_uac_right_post ind l r
       (a:int list) (i:int) (v:int) (c:int) <=>
      !c1:int. !r':ntp4vc_sumrange_uac_tree.
        c1 - (c + (&1:int)) <= ntp4vc_sumrange_uac_depth r /\
        ntp4vc_sumrange_uac_low
          (ntp4vc_sumrange_uac_indexes_of r') =
          ntp4vc_sumrange_uac_low
            (ntp4vc_sumrange_uac_indexes_of r) /\
        ntp4vc_sumrange_uac_high
          (ntp4vc_sumrange_uac_indexes_of r') =
          ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of r) /\
        ntp4vc_sumrange_uac_is_tree_for r'
          (ntp4vc_sumrange_uac_update a i v)
          (ntp4vc_sumrange_uac_low
            (ntp4vc_sumrange_uac_indexes_of r'))
          (ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of r'))
        ==>
        c1 - c <=
          ntp4vc_sumrange_uac_depth
            (NTP4VCSumrangeUACNode ind l r) /\
        ntp4vc_sumrange_uac_low
          (ntp4vc_sumrange_uac_indexes_of
            (ntp4vc_sumrange_uac_new_right ind l r' a i v)) =
          ntp4vc_sumrange_uac_low ind /\
        ntp4vc_sumrange_uac_high
          (ntp4vc_sumrange_uac_indexes_of
            (ntp4vc_sumrange_uac_new_right ind l r' a i v)) =
          ntp4vc_sumrange_uac_high ind /\
        ntp4vc_sumrange_uac_is_tree_for
          (ntp4vc_sumrange_uac_new_right ind l r' a i v)
          (ntp4vc_sumrange_uac_update a i v)
          (ntp4vc_sumrange_uac_low
            (ntp4vc_sumrange_uac_indexes_of
              (ntp4vc_sumrange_uac_new_right ind l r' a i v)))
          (ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of
              (ntp4vc_sumrange_uac_new_right ind l r' a i v)))`;;

let ntp4vc_sumrange_uac_vc =
  new_recursive_definition ntp4vc_sumrange_uac_tree_RECURSION
   `(!ind a i v c.
       ntp4vc_sumrange_uac_vc
         (NTP4VCSumrangeUACLeaf ind)
         (a:int list) (i:int) (v:int) (c:int) =
       ntp4vc_sumrange_uac_leaf_vc ind a i v c) /\
    (!ind l r a i v c.
       ntp4vc_sumrange_uac_vc
         (NTP4VCSumrangeUACNode ind l r)
         (a:int list) (i:int) (v:int) (c:int) =
       if i <
          ntp4vc_sumrange_uac_high
            (ntp4vc_sumrange_uac_indexes_of l)
       then
         ntp4vc_sumrange_uac_left_pre ind l r a i /\
         ntp4vc_sumrange_uac_left_post ind l r a i v c
       else
         ntp4vc_sumrange_uac_right_pre ind l r a i /\
         ntp4vc_sumrange_uac_right_post ind l r a i v c)`;;

let statement =
 `!t:ntp4vc_sumrange_uac_tree.
  !a:int list.
  !i v c:int.
    ntp4vc_sumrange_uac_is_tree_for t a
      (ntp4vc_sumrange_uac_low
        (ntp4vc_sumrange_uac_indexes_of t))
      (ntp4vc_sumrange_uac_high
        (ntp4vc_sumrange_uac_indexes_of t))
    ==>
    ntp4vc_sumrange_uac_low
      (ntp4vc_sumrange_uac_indexes_of t) <= i
    ==>
    i < ntp4vc_sumrange_uac_high
          (ntp4vc_sumrange_uac_indexes_of t)
    ==>
    ntp4vc_sumrange_uac_vc t a i v c`;;
