(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_update_auxqtvc: the cumulative range-sum tree
  point-update verification condition, including the selected recursive-call
  bounds, rebuilt-tree intervals, and preservation of the updated tree
  invariant. This file contains no proof.
*)

let ntp4vc_sumrange_ua_indexes_INDUCT,
    ntp4vc_sumrange_ua_indexes_RECURSION =
  define_type
    "ntp4vc_sumrange_ua_indexes =
       NTP4VCSumrangeUAIndexes int int int";;

let ntp4vc_sumrange_ua_low =
  new_recursive_definition ntp4vc_sumrange_ua_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_ua_low
        (NTP4VCSumrangeUAIndexes lo hi s) = lo`;;

let ntp4vc_sumrange_ua_high =
  new_recursive_definition ntp4vc_sumrange_ua_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_ua_high
        (NTP4VCSumrangeUAIndexes lo hi s) = hi`;;

let ntp4vc_sumrange_ua_isum =
  new_recursive_definition ntp4vc_sumrange_ua_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_ua_isum
        (NTP4VCSumrangeUAIndexes lo hi s) = s`;;

let ntp4vc_sumrange_ua_tree_INDUCT,
    ntp4vc_sumrange_ua_tree_RECURSION =
  define_type
    "ntp4vc_sumrange_ua_tree =
       NTP4VCSumrangeUALeaf ntp4vc_sumrange_ua_indexes
     | NTP4VCSumrangeUANode
         ntp4vc_sumrange_ua_indexes
         ntp4vc_sumrange_ua_tree
         ntp4vc_sumrange_ua_tree";;

let ntp4vc_sumrange_ua_indexes_of =
  new_recursive_definition ntp4vc_sumrange_ua_tree_RECURSION
   `(!ind.
       ntp4vc_sumrange_ua_indexes_of
         (NTP4VCSumrangeUALeaf ind) = ind) /\
    (!ind l r.
       ntp4vc_sumrange_ua_indexes_of
         (NTP4VCSumrangeUANode ind l r) = ind)`;;

let ntp4vc_sumrange_ua_to_num = new_definition
 `ntp4vc_sumrange_ua_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sumrange_ua_nth = new_definition
 `ntp4vc_sumrange_ua_nth (a:int list) (i:int) =
    if ntp4vc_sumrange_ua_to_num i < LENGTH a
    then EL (ntp4vc_sumrange_ua_to_num i) a
    else (&0:int)`;;

let ntp4vc_sumrange_ua_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:int. ntp4vc_sumrange_ua_update_nat [] n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       ntp4vc_sumrange_ua_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h
         (ntp4vc_sumrange_ua_update_nat t (PRE n) x))`;;

let ntp4vc_sumrange_ua_update = new_definition
 `ntp4vc_sumrange_ua_update (a:int list) (i:int) (x:int) =
    ntp4vc_sumrange_ua_update_nat a
      (ntp4vc_sumrange_ua_to_num i) x`;;

let ntp4vc_sumrange_ua_sum_nat =
  new_recursive_definition num_RECURSION
   `(!a:int list. !lower:int.
       ntp4vc_sumrange_ua_sum_nat a lower 0 = (&0:int)) /\
    (!a:int list. !lower:int. !n:num.
       ntp4vc_sumrange_ua_sum_nat a lower (SUC n) =
       ntp4vc_sumrange_ua_nth a lower +
       ntp4vc_sumrange_ua_sum_nat
         a (lower + (&1:int)) n)`;;

let ntp4vc_sumrange_ua_sum = new_definition
 `ntp4vc_sumrange_ua_sum
    (a:int list) (lower:int) (upper:int) =
    ntp4vc_sumrange_ua_sum_nat a lower
      (ntp4vc_sumrange_ua_to_num (upper - lower))`;;

let ntp4vc_sumrange_ua_cdiv = new_definition
 `ntp4vc_sumrange_ua_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let ntp4vc_sumrange_ua_is_indexes_for = new_definition
 `ntp4vc_sumrange_ua_is_indexes_for
    (ind:ntp4vc_sumrange_ua_indexes)
    (a:int list) (i:int) (j:int) <=>
    ntp4vc_sumrange_ua_low ind = i /\
    ntp4vc_sumrange_ua_high ind = j /\
    (&0:int) <= i /\ i < j /\ j <= (&(LENGTH a):int) /\
    ntp4vc_sumrange_ua_isum ind =
      ntp4vc_sumrange_ua_sum a i j`;;

let ntp4vc_sumrange_ua_is_tree_for =
  new_recursive_definition ntp4vc_sumrange_ua_tree_RECURSION
   `(!ind a i j.
       ntp4vc_sumrange_ua_is_tree_for
         (NTP4VCSumrangeUALeaf ind)
         (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_ua_is_indexes_for ind a i j /\
        j = i + (&1:int))) /\
    (!ind l r a i j.
       ntp4vc_sumrange_ua_is_tree_for
         (NTP4VCSumrangeUANode ind l r)
         (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_ua_is_indexes_for ind a i j /\
        i = ntp4vc_sumrange_ua_low
              (ntp4vc_sumrange_ua_indexes_of l) /\
        j = ntp4vc_sumrange_ua_high
              (ntp4vc_sumrange_ua_indexes_of r) /\
        (let m =
           ntp4vc_sumrange_ua_high
             (ntp4vc_sumrange_ua_indexes_of l) in
         m = ntp4vc_sumrange_ua_low
               (ntp4vc_sumrange_ua_indexes_of r) /\
         i < m /\ m < j /\
         m = ntp4vc_sumrange_ua_cdiv (i + j) (&2:int) /\
         ntp4vc_sumrange_ua_is_tree_for l a i m /\
         ntp4vc_sumrange_ua_is_tree_for r a m j)))`;;

let ntp4vc_sumrange_ua_is_child =
  new_recursive_definition ntp4vc_sumrange_ua_tree_RECURSION
   `(!child ind.
       ntp4vc_sumrange_ua_is_child
         (child:ntp4vc_sumrange_ua_tree)
         (NTP4VCSumrangeUALeaf ind) = F) /\
    (!child ind l r.
       ntp4vc_sumrange_ua_is_child
         (child:ntp4vc_sumrange_ua_tree)
         (NTP4VCSumrangeUANode ind l r) =
       (child = l \/ child = r))`;;

let ntp4vc_sumrange_ua_selected_call =
  new_recursive_definition ntp4vc_sumrange_ua_tree_RECURSION
   `(!ind a i.
       ntp4vc_sumrange_ua_selected_call
         (NTP4VCSumrangeUALeaf ind)
         (a:int list) (i:int) = T) /\
    (!ind l r a i.
       ntp4vc_sumrange_ua_selected_call
         (NTP4VCSumrangeUANode ind l r)
         (a:int list) (i:int) =
       if i <
          ntp4vc_sumrange_ua_high
            (ntp4vc_sumrange_ua_indexes_of l)
       then
         ntp4vc_sumrange_ua_is_child l
           (NTP4VCSumrangeUANode ind l r) /\
         ntp4vc_sumrange_ua_is_tree_for l a
           (ntp4vc_sumrange_ua_low
             (ntp4vc_sumrange_ua_indexes_of l))
           (ntp4vc_sumrange_ua_high
             (ntp4vc_sumrange_ua_indexes_of l)) /\
         ntp4vc_sumrange_ua_low
           (ntp4vc_sumrange_ua_indexes_of l) <= i /\
         i < ntp4vc_sumrange_ua_high
               (ntp4vc_sumrange_ua_indexes_of l)
       else
         ntp4vc_sumrange_ua_is_child r
           (NTP4VCSumrangeUANode ind l r) /\
         ntp4vc_sumrange_ua_is_tree_for r a
           (ntp4vc_sumrange_ua_low
             (ntp4vc_sumrange_ua_indexes_of r))
           (ntp4vc_sumrange_ua_high
             (ntp4vc_sumrange_ua_indexes_of r)) /\
         ntp4vc_sumrange_ua_low
           (ntp4vc_sumrange_ua_indexes_of r) <= i /\
         i < ntp4vc_sumrange_ua_high
               (ntp4vc_sumrange_ua_indexes_of r))`;;

let ntp4vc_sumrange_ua_updated_indexes = new_definition
 `ntp4vc_sumrange_ua_updated_indexes
    ind (a:int list) (i:int) (v:int) =
    NTP4VCSumrangeUAIndexes
      (ntp4vc_sumrange_ua_low ind)
      (ntp4vc_sumrange_ua_high ind)
      (ntp4vc_sumrange_ua_isum ind +
       (v - ntp4vc_sumrange_ua_nth a i))`;;

let ntp4vc_sumrange_ua_result_premise =
  new_recursive_definition ntp4vc_sumrange_ua_tree_RECURSION
   `(!ind a i v t' delta.
       ntp4vc_sumrange_ua_result_premise
         (NTP4VCSumrangeUALeaf ind)
         (a:int list) (i:int) (v:int)
         (t':ntp4vc_sumrange_ua_tree) (delta:int) =
       (t' =
          NTP4VCSumrangeUALeaf
            (NTP4VCSumrangeUAIndexes
              (ntp4vc_sumrange_ua_low ind)
              (ntp4vc_sumrange_ua_high ind) v) /\
        delta = v - ntp4vc_sumrange_ua_isum ind)) /\
    (!ind l r a i v t' delta.
       ntp4vc_sumrange_ua_result_premise
         (NTP4VCSumrangeUANode ind l r)
         (a:int list) (i:int) (v:int)
         (t':ntp4vc_sumrange_ua_tree) (delta:int) =
       if i <
          ntp4vc_sumrange_ua_high
            (ntp4vc_sumrange_ua_indexes_of l)
       then
         ?l':ntp4vc_sumrange_ua_tree.
           ntp4vc_sumrange_ua_low
             (ntp4vc_sumrange_ua_indexes_of l') =
             ntp4vc_sumrange_ua_low
               (ntp4vc_sumrange_ua_indexes_of l) /\
           ntp4vc_sumrange_ua_high
             (ntp4vc_sumrange_ua_indexes_of l') =
             ntp4vc_sumrange_ua_high
               (ntp4vc_sumrange_ua_indexes_of l) /\
           ntp4vc_sumrange_ua_is_tree_for l'
             (ntp4vc_sumrange_ua_update a i v)
             (ntp4vc_sumrange_ua_low
               (ntp4vc_sumrange_ua_indexes_of l'))
             (ntp4vc_sumrange_ua_high
               (ntp4vc_sumrange_ua_indexes_of l')) /\
           t' =
             NTP4VCSumrangeUANode
               (ntp4vc_sumrange_ua_updated_indexes ind a i v)
               l' r /\
           delta = v - ntp4vc_sumrange_ua_nth a i
       else
         ?r':ntp4vc_sumrange_ua_tree.
           ntp4vc_sumrange_ua_low
             (ntp4vc_sumrange_ua_indexes_of r') =
             ntp4vc_sumrange_ua_low
               (ntp4vc_sumrange_ua_indexes_of r) /\
           ntp4vc_sumrange_ua_high
             (ntp4vc_sumrange_ua_indexes_of r') =
             ntp4vc_sumrange_ua_high
               (ntp4vc_sumrange_ua_indexes_of r) /\
           ntp4vc_sumrange_ua_is_tree_for r'
             (ntp4vc_sumrange_ua_update a i v)
             (ntp4vc_sumrange_ua_low
               (ntp4vc_sumrange_ua_indexes_of r'))
             (ntp4vc_sumrange_ua_high
               (ntp4vc_sumrange_ua_indexes_of r')) /\
           t' =
             NTP4VCSumrangeUANode
               (ntp4vc_sumrange_ua_updated_indexes ind a i v)
               l r' /\
           delta = v - ntp4vc_sumrange_ua_nth a i)`;;

let ntp4vc_sumrange_ua_result_conclusion = new_definition
 `ntp4vc_sumrange_ua_result_conclusion
    (t:ntp4vc_sumrange_ua_tree)
    (a:int list) (i:int) (v:int)
    (t':ntp4vc_sumrange_ua_tree) (delta:int) <=>
    delta = v - ntp4vc_sumrange_ua_nth a i /\
    ntp4vc_sumrange_ua_low
      (ntp4vc_sumrange_ua_indexes_of t') =
      ntp4vc_sumrange_ua_low
        (ntp4vc_sumrange_ua_indexes_of t) /\
    ntp4vc_sumrange_ua_high
      (ntp4vc_sumrange_ua_indexes_of t') =
      ntp4vc_sumrange_ua_high
        (ntp4vc_sumrange_ua_indexes_of t) /\
    ntp4vc_sumrange_ua_is_tree_for t'
      (ntp4vc_sumrange_ua_update a i v)
      (ntp4vc_sumrange_ua_low
        (ntp4vc_sumrange_ua_indexes_of t'))
      (ntp4vc_sumrange_ua_high
        (ntp4vc_sumrange_ua_indexes_of t'))`;;

let statement =
 `!t:ntp4vc_sumrange_ua_tree.
  !a:int list.
  !i v:int.
    ntp4vc_sumrange_ua_is_tree_for t a
      (ntp4vc_sumrange_ua_low
        (ntp4vc_sumrange_ua_indexes_of t))
      (ntp4vc_sumrange_ua_high
        (ntp4vc_sumrange_ua_indexes_of t))
    ==>
    ntp4vc_sumrange_ua_low
      (ntp4vc_sumrange_ua_indexes_of t) <= i
    ==>
    i < ntp4vc_sumrange_ua_high
          (ntp4vc_sumrange_ua_indexes_of t)
    ==>
    ntp4vc_sumrange_ua_selected_call t a i /\
    (!t':ntp4vc_sumrange_ua_tree.
     !delta:int.
       ntp4vc_sumrange_ua_result_premise t a i v t' delta
       ==>
       ntp4vc_sumrange_ua_result_conclusion t a i v t' delta)`;;
