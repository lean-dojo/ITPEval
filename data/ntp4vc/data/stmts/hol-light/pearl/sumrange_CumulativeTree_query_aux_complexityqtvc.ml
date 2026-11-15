(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_query_aux_complexityqtvc: the verification
  condition for a cumulative-tree range-sum query, preserving tree and
  interval invariants, recursive-call obligations, range-sum composition,
  and the depth-based credit bound. This file contains no proof.
*)

let ntp4vc_sumrange_indexes_INDUCT,
    ntp4vc_sumrange_indexes_RECURSION =
  define_type
    "ntp4vc_sumrange_indexes =
       NTP4VCSumrangeIndexes int int int";;

let ntp4vc_sumrange_low =
  new_recursive_definition ntp4vc_sumrange_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_low (NTP4VCSumrangeIndexes lo hi s) = lo`;;

let ntp4vc_sumrange_high =
  new_recursive_definition ntp4vc_sumrange_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_high (NTP4VCSumrangeIndexes lo hi s) = hi`;;

let ntp4vc_sumrange_isum =
  new_recursive_definition ntp4vc_sumrange_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_isum (NTP4VCSumrangeIndexes lo hi s) = s`;;

let ntp4vc_sumrange_tree_INDUCT,
    ntp4vc_sumrange_tree_RECURSION =
  define_type
    "ntp4vc_sumrange_tree =
       NTP4VCSumrangeLeaf ntp4vc_sumrange_indexes
     | NTP4VCSumrangeNode
         ntp4vc_sumrange_indexes
         ntp4vc_sumrange_tree
         ntp4vc_sumrange_tree";;

let ntp4vc_sumrange_indexes_of =
  new_recursive_definition ntp4vc_sumrange_tree_RECURSION
   `(!ind.
       ntp4vc_sumrange_indexes_of (NTP4VCSumrangeLeaf ind) = ind) /\
    (!ind l r.
       ntp4vc_sumrange_indexes_of (NTP4VCSumrangeNode ind l r) = ind)`;;

let ntp4vc_sumrange_to_num = new_definition
 `ntp4vc_sumrange_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sumrange_nth = new_definition
 `ntp4vc_sumrange_nth (a:int list) (i:int) =
    if ntp4vc_sumrange_to_num i < LENGTH a
    then EL (ntp4vc_sumrange_to_num i) a
    else (&0:int)`;;

let ntp4vc_sumrange_sum_nat =
  new_recursive_definition num_RECURSION
   `(!a:int list. !lower:int.
       ntp4vc_sumrange_sum_nat a lower 0 = (&0:int)) /\
    (!a:int list. !lower:int. !n:num.
       ntp4vc_sumrange_sum_nat a lower (SUC n) =
       ntp4vc_sumrange_nth a lower +
       ntp4vc_sumrange_sum_nat a (lower + (&1:int)) n)`;;

let ntp4vc_sumrange_sum = new_definition
 `ntp4vc_sumrange_sum (a:int list) (lower:int) (upper:int) =
    ntp4vc_sumrange_sum_nat a lower
      (ntp4vc_sumrange_to_num (upper - lower))`;;

let ntp4vc_sumrange_cdiv = new_definition
 `ntp4vc_sumrange_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let ntp4vc_sumrange_int_max = new_definition
 `ntp4vc_sumrange_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let ntp4vc_sumrange_is_indexes_for = new_definition
 `ntp4vc_sumrange_is_indexes_for
    (ind:ntp4vc_sumrange_indexes)
    (a:int list) (i:int) (j:int) <=>
    ntp4vc_sumrange_low ind = i /\
    ntp4vc_sumrange_high ind = j /\
    (&0:int) <= i /\ i < j /\ j <= (&(LENGTH a):int) /\
    ntp4vc_sumrange_isum ind = ntp4vc_sumrange_sum a i j`;;

let ntp4vc_sumrange_is_tree_for =
  new_recursive_definition ntp4vc_sumrange_tree_RECURSION
   `(!ind a i j.
       ntp4vc_sumrange_is_tree_for
         (NTP4VCSumrangeLeaf ind) (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_is_indexes_for ind a i j /\
        j = i + (&1:int))) /\
    (!ind l r a i j.
       ntp4vc_sumrange_is_tree_for
         (NTP4VCSumrangeNode ind l r) (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_is_indexes_for ind a i j /\
        i = ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of l) /\
        j = ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of r) /\
        (let m =
           ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of l) in
         m = ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of r) /\
         i < m /\ m < j /\
         m = ntp4vc_sumrange_cdiv (i + j) (&2:int) /\
         ntp4vc_sumrange_is_tree_for l a i m /\
         ntp4vc_sumrange_is_tree_for r a m j)))`;;

let ntp4vc_sumrange_depth =
  new_recursive_definition ntp4vc_sumrange_tree_RECURSION
   `(!ind.
       ntp4vc_sumrange_depth (NTP4VCSumrangeLeaf ind) = (&1:int)) /\
    (!ind l r.
       ntp4vc_sumrange_depth (NTP4VCSumrangeNode ind l r) =
       (&1:int) +
       ntp4vc_sumrange_int_max
         (ntp4vc_sumrange_depth l)
         (ntp4vc_sumrange_depth r))`;;

let ntp4vc_sumrange_is_child =
  new_recursive_definition ntp4vc_sumrange_tree_RECURSION
   `(!child ind.
       ntp4vc_sumrange_is_child
         (child:ntp4vc_sumrange_tree)
         (NTP4VCSumrangeLeaf ind) = F) /\
    (!child ind l r.
       ntp4vc_sumrange_is_child
         (child:ntp4vc_sumrange_tree)
         (NTP4VCSumrangeNode ind l r) =
       (child = l \/ child = r))`;;

let ntp4vc_sumrange_complexity_bound = new_definition
 `ntp4vc_sumrange_complexity_bound
    (t:ntp4vc_sumrange_tree) (i:int) (j:int) =
    if i = ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of t) /\
       j = ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of t)
    then (&1:int)
    else if
      i = ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of t) \/
      j = ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of t)
    then (&2:int) * ntp4vc_sumrange_depth t
    else (&4:int) * ntp4vc_sumrange_depth t`;;

let ntp4vc_sumrange_recursive_call_pre = new_definition
 `ntp4vc_sumrange_recursive_call_pre
    (parent:ntp4vc_sumrange_tree)
    (child:ntp4vc_sumrange_tree)
    (a:int list) (i:int) (j:int) <=>
    ntp4vc_sumrange_is_child child parent /\
    ntp4vc_sumrange_is_tree_for child a
      (ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of child))
      (ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of child)) /\
    (&0:int) <=
      ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of child) /\
    ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of child) <= i /\
    i < j /\
    j <= ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of child) /\
    ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of child) <=
      (&(LENGTH a):int)`;;

let ntp4vc_sumrange_query_aux_complexity_vc =
  new_recursive_definition ntp4vc_sumrange_tree_RECURSION
   `(!ind a i j c.
       ntp4vc_sumrange_query_aux_complexity_vc
         (NTP4VCSumrangeLeaf ind) (a:int list)
         (i:int) (j:int) (c:int) =
       (c + (&1:int) - c <=
          ntp4vc_sumrange_complexity_bound
            (NTP4VCSumrangeLeaf ind) i j /\
        ntp4vc_sumrange_isum ind =
          ntp4vc_sumrange_sum a i j)) /\
    (!ind l r a i j c.
       ntp4vc_sumrange_query_aux_complexity_vc
         (NTP4VCSumrangeNode ind l r) (a:int list)
         (i:int) (j:int) (c:int) =
       (!o1:bool.
          (if i = ntp4vc_sumrange_low ind
           then o1 =
             (if j = ntp4vc_sumrange_high ind then T else F)
           else o1 = F)
          ==>
          if o1 = T then
            c + (&1:int) - c <=
              ntp4vc_sumrange_complexity_bound
                (NTP4VCSumrangeNode ind l r) i j /\
            ntp4vc_sumrange_isum ind =
              ntp4vc_sumrange_sum a i j
          else
            let m =
              ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of l) in
            if j <= m then
              ntp4vc_sumrange_recursive_call_pre
                (NTP4VCSumrangeNode ind l r) l a i j /\
              (!c1:int.
                 c1 - (c + (&1:int)) <=
                   ntp4vc_sumrange_complexity_bound l i j
                 ==>
                 c1 - c <=
                   ntp4vc_sumrange_complexity_bound
                     (NTP4VCSumrangeNode ind l r) i j)
            else if m <= i then
              ntp4vc_sumrange_recursive_call_pre
                (NTP4VCSumrangeNode ind l r) r a i j /\
              (!c1:int.
                 c1 - (c + (&1:int)) <=
                   ntp4vc_sumrange_complexity_bound r i j
                 ==>
                 c1 - c <=
                   ntp4vc_sumrange_complexity_bound
                     (NTP4VCSumrangeNode ind l r) i j)
            else
              ntp4vc_sumrange_recursive_call_pre
                (NTP4VCSumrangeNode ind l r) r a m j /\
              (!c1:int.
                 c1 - (c + (&1:int)) <=
                   ntp4vc_sumrange_complexity_bound r m j
                 ==>
                 ntp4vc_sumrange_recursive_call_pre
                   (NTP4VCSumrangeNode ind l r) l a i m /\
                 (!c2:int.
                    c2 - c1 <=
                      ntp4vc_sumrange_complexity_bound l i m
                    ==>
                    c2 - c <=
                      ntp4vc_sumrange_complexity_bound
                        (NTP4VCSumrangeNode ind l r) i j /\
                    ntp4vc_sumrange_sum a i m +
                      ntp4vc_sumrange_sum a m j =
                    ntp4vc_sumrange_sum a i j))))`;;

let statement =
 `!t:ntp4vc_sumrange_tree.
  !a:int list.
  !i j c:int.
    ntp4vc_sumrange_is_tree_for t a
      (ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of t))
      (ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of t))
    ==>
    (&0:int) <=
      ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of t)
    ==>
    ntp4vc_sumrange_low (ntp4vc_sumrange_indexes_of t) <= i
    ==>
    i < j
    ==>
    j <= ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of t)
    ==>
    ntp4vc_sumrange_high (ntp4vc_sumrange_indexes_of t) <=
      (&(LENGTH a):int)
    ==>
    ntp4vc_sumrange_query_aux_complexity_vc t a i j c`;;
