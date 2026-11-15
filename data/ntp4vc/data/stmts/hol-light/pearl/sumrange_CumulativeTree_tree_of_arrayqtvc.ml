(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_tree_of_arrayqtvc: the verification condition
  for constructing a cumulative range-sum tree from a nonempty integer-array
  interval, including midpoint recursion, termination obligations, and the
  resulting tree invariant. This file contains no proof.
*)

let ntp4vc_sumrange_toa_indexes_INDUCT,
    ntp4vc_sumrange_toa_indexes_RECURSION =
  define_type
    "ntp4vc_sumrange_toa_indexes =
       NTP4VCSumrangeToAIndexes int int int";;

let ntp4vc_sumrange_toa_low =
  new_recursive_definition ntp4vc_sumrange_toa_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_toa_low
        (NTP4VCSumrangeToAIndexes lo hi s) = lo`;;

let ntp4vc_sumrange_toa_high =
  new_recursive_definition ntp4vc_sumrange_toa_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_toa_high
        (NTP4VCSumrangeToAIndexes lo hi s) = hi`;;

let ntp4vc_sumrange_toa_isum =
  new_recursive_definition ntp4vc_sumrange_toa_indexes_RECURSION
   `!lo hi s:int.
      ntp4vc_sumrange_toa_isum
        (NTP4VCSumrangeToAIndexes lo hi s) = s`;;

let ntp4vc_sumrange_toa_tree_INDUCT,
    ntp4vc_sumrange_toa_tree_RECURSION =
  define_type
    "ntp4vc_sumrange_toa_tree =
       NTP4VCSumrangeToALeaf ntp4vc_sumrange_toa_indexes
     | NTP4VCSumrangeToANode
         ntp4vc_sumrange_toa_indexes
         ntp4vc_sumrange_toa_tree
         ntp4vc_sumrange_toa_tree";;

let ntp4vc_sumrange_toa_indexes_of =
  new_recursive_definition ntp4vc_sumrange_toa_tree_RECURSION
   `(!ind.
       ntp4vc_sumrange_toa_indexes_of
         (NTP4VCSumrangeToALeaf ind) = ind) /\
    (!ind l r.
       ntp4vc_sumrange_toa_indexes_of
         (NTP4VCSumrangeToANode ind l r) = ind)`;;

let ntp4vc_sumrange_toa_to_num = new_definition
 `ntp4vc_sumrange_toa_to_num (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_sumrange_toa_nth = new_definition
 `ntp4vc_sumrange_toa_nth (a:int list) (i:int) =
    if ntp4vc_sumrange_toa_to_num i < LENGTH a
    then EL (ntp4vc_sumrange_toa_to_num i) a
    else (&0:int)`;;

let ntp4vc_sumrange_toa_sum_nat =
  new_recursive_definition num_RECURSION
   `(!a:int list. !lower:int.
       ntp4vc_sumrange_toa_sum_nat a lower 0 = (&0:int)) /\
    (!a:int list. !lower:int. !n:num.
       ntp4vc_sumrange_toa_sum_nat a lower (SUC n) =
       ntp4vc_sumrange_toa_nth a lower +
       ntp4vc_sumrange_toa_sum_nat a (lower + (&1:int)) n)`;;

let ntp4vc_sumrange_toa_sum = new_definition
 `ntp4vc_sumrange_toa_sum (a:int list) (lower:int) (upper:int) =
    ntp4vc_sumrange_toa_sum_nat a lower
      (ntp4vc_sumrange_toa_to_num (upper - lower))`;;

let ntp4vc_sumrange_toa_cdiv = new_definition
 `ntp4vc_sumrange_toa_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let ntp4vc_sumrange_toa_is_indexes_for = new_definition
 `ntp4vc_sumrange_toa_is_indexes_for
    (ind:ntp4vc_sumrange_toa_indexes)
    (a:int list) (i:int) (j:int) <=>
    ntp4vc_sumrange_toa_low ind = i /\
    ntp4vc_sumrange_toa_high ind = j /\
    (&0:int) <= i /\
    i < j /\
    j <= (&(LENGTH a):int) /\
    ntp4vc_sumrange_toa_isum ind =
      ntp4vc_sumrange_toa_sum a i j`;;

let ntp4vc_sumrange_toa_is_tree_for =
  new_recursive_definition ntp4vc_sumrange_toa_tree_RECURSION
   `(!ind a i j.
       ntp4vc_sumrange_toa_is_tree_for
         (NTP4VCSumrangeToALeaf ind) (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_toa_is_indexes_for ind a i j /\
        j = i + (&1:int))) /\
    (!ind l r a i j.
       ntp4vc_sumrange_toa_is_tree_for
         (NTP4VCSumrangeToANode ind l r)
         (a:int list) (i:int) (j:int) =
       (ntp4vc_sumrange_toa_is_indexes_for ind a i j /\
        i = ntp4vc_sumrange_toa_low
              (ntp4vc_sumrange_toa_indexes_of l) /\
        j = ntp4vc_sumrange_toa_high
              (ntp4vc_sumrange_toa_indexes_of r) /\
        (let m =
           ntp4vc_sumrange_toa_high
             (ntp4vc_sumrange_toa_indexes_of l) in
         m = ntp4vc_sumrange_toa_low
               (ntp4vc_sumrange_toa_indexes_of r) /\
         i < m /\
         m < j /\
         m = ntp4vc_sumrange_toa_cdiv (i + j) (&2:int) /\
         ntp4vc_sumrange_toa_is_tree_for l a i m /\
         ntp4vc_sumrange_toa_is_tree_for r a m j)))`;;

let statement =
 `!i j:int. !a:int list.
    (&0:int) <= i
    ==>
    i < j
    ==>
    j <= (&(LENGTH a):int)
    ==>
    (let o1 = i + (&1:int) in
     (if o1 = j then
        (&0:int) <= i /\ i < (&(LENGTH a):int)
      else
        ~((&2:int) = (&0:int)) /\
        (let m = ntp4vc_sumrange_toa_cdiv (i + j) (&2:int) in
         (((&0:int) <= j - i /\ m - i < j - i) /\
          (&0:int) <= i /\ i < m /\ m <= (&(LENGTH a):int)) /\
         (!l:ntp4vc_sumrange_toa_tree.
            ntp4vc_sumrange_toa_is_tree_for l a i m
            ==>
            ((&0:int) <= j - i /\ j - m < j - i) /\
            (&0:int) <= m /\ m < j /\
            j <= (&(LENGTH a):int))))
     /\
     (!result:ntp4vc_sumrange_toa_tree.
        (if o1 = j then
           result =
             NTP4VCSumrangeToALeaf
               (NTP4VCSumrangeToAIndexes
                 i j (ntp4vc_sumrange_toa_nth a i))
         else
           let m = ntp4vc_sumrange_toa_cdiv (i + j) (&2:int) in
           ?l:ntp4vc_sumrange_toa_tree.
             ntp4vc_sumrange_toa_is_tree_for l a i m /\
             (?r:ntp4vc_sumrange_toa_tree.
                ntp4vc_sumrange_toa_is_tree_for r a m j /\
                result =
                  NTP4VCSumrangeToANode
                    (NTP4VCSumrangeToAIndexes
                      i j
                      (ntp4vc_sumrange_toa_isum
                         (ntp4vc_sumrange_toa_indexes_of l) +
                       ntp4vc_sumrange_toa_isum
                         (ntp4vc_sumrange_toa_indexes_of r)))
                    l r))
        ==>
        ntp4vc_sumrange_toa_is_tree_for result a i j))`;;
