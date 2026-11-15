(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sumrange_CumulativeTree_query_auxqtvc: the auxiliary cumulative-tree
  range-sum query verification condition, preserving recursive subtree
  invariants and establishing the returned integer interval sum. This file
  contains no proof.
*)

let sr_indexes_INDUCT,sr_indexes_RECURSION = define_type
  "sr_indexes = SRIndexes int int int";;

let sr_low =
  new_recursive_definition sr_indexes_RECURSION
    `!l h s. sr_low (SRIndexes l h s) = l`;;

let sr_high =
  new_recursive_definition sr_indexes_RECURSION
    `!l h s. sr_high (SRIndexes l h s) = h`;;

let sr_isum =
  new_recursive_definition sr_indexes_RECURSION
    `!l h s. sr_isum (SRIndexes l h s) = s`;;

let sr_tree_INDUCT,sr_tree_RECURSION = define_type
  "sr_tree = SRLeaf sr_indexes | SRNode sr_indexes sr_tree sr_tree";;

let sr_indexes_of =
  new_recursive_definition sr_tree_RECURSION
    `(!ind. sr_indexes_of (SRLeaf ind) = ind) /\
     (!ind l r. sr_indexes_of (SRNode ind l r) = ind)`;;

let sr_array_sum_num =
  new_recursive_definition num_RECURSION
    `(!a:int list. !start:num.
        sr_array_sum_num a start 0 = (&0:int)) /\
     (!a:int list. !start:num. !n:num.
        sr_array_sum_num a start (SUC n) =
        sr_array_sum_num a start n +
          (if start + n < LENGTH a
           then EL (start + n) a
           else (&0:int)))`;;

let sr_array_sum = new_definition
  `sr_array_sum (a:int list) (i:int) (j:int) =
     sr_array_sum_num
       a (num_of_int i) (num_of_int (j - i))`;;

let sr_cdiv = new_definition
  `sr_cdiv (n:int) (d:int) =
     if (&0:int) <= n
     then if (&0:int) <= d then n div d else --(n div --d)
     else if (&0:int) <= d then --(--n div d) else --n div --d`;;

let sr_is_indexes_for = new_definition
  `sr_is_indexes_for
      (ind:sr_indexes) (a:int list) (i:int) (j:int) <=>
     sr_low ind = i /\
     sr_high ind = j /\
     (&0:int) <= i /\
     i < j /\
     j <= (&(LENGTH a):int) /\
     sr_isum ind = sr_array_sum a i j`;;

let sr_is_tree_for =
  new_recursive_definition sr_tree_RECURSION
    `(!ind a i j.
        sr_is_tree_for (SRLeaf ind) a i j <=>
        sr_is_indexes_for ind a i j /\ j = i + (&1:int)) /\
     (!ind l r a i j.
        sr_is_tree_for (SRNode ind l r) a i j <=>
        sr_is_indexes_for ind a i j /\
        i = sr_low (sr_indexes_of l) /\
        j = sr_high (sr_indexes_of r) /\
        (let m = sr_high (sr_indexes_of l) in
         m = sr_low (sr_indexes_of r) /\
         i < m /\
         m < j /\
         m = sr_cdiv (i + j) (&2:int) /\
         sr_is_tree_for l a i m /\
         sr_is_tree_for r a m j))`;;

let sr_is_child =
  new_recursive_definition sr_tree_RECURSION
    `(!ind u. sr_is_child (SRLeaf ind) u <=> F) /\
     (!ind l r u.
        sr_is_child (SRNode ind l r) u <=> u = l \/ u = r)`;;

let sr_query_aux_vc =
  new_recursive_definition sr_tree_RECURSION
    `(!ind a i j.
        sr_query_aux_vc (SRLeaf ind) a i j <=>
        (!result:int.
           result = sr_isum ind
           ==> result = sr_array_sum a i j)) /\
     (!ind l r a i j.
        sr_query_aux_vc (SRNode ind l r) a i j <=>
        (!o1:bool.
           (if i = sr_low ind
            then o1 = (if j = sr_high ind then T else F)
            else o1 = F)
           ==> ~(o1 = T)
           ==> (let m = sr_high (sr_indexes_of l) in
                if j <= m then
                  sr_is_child (SRNode ind l r) l /\
                  sr_is_tree_for
                    l a (sr_low (sr_indexes_of l))
                        (sr_high (sr_indexes_of l)) /\
                  (&0:int) <= sr_low (sr_indexes_of l) /\
                  sr_low (sr_indexes_of l) <= i /\
                  i < j /\
                  j <= sr_high (sr_indexes_of l) /\
                  sr_high (sr_indexes_of l) <= (&(LENGTH a):int)
                else if m <= i then
                  sr_is_child (SRNode ind l r) r /\
                  sr_is_tree_for
                    r a (sr_low (sr_indexes_of r))
                        (sr_high (sr_indexes_of r)) /\
                  (&0:int) <= sr_low (sr_indexes_of r) /\
                  sr_low (sr_indexes_of r) <= i /\
                  i < j /\
                  j <= sr_high (sr_indexes_of r) /\
                  sr_high (sr_indexes_of r) <= (&(LENGTH a):int)
                else
                  (sr_is_child (SRNode ind l r) r /\
                   sr_is_tree_for
                     r a (sr_low (sr_indexes_of r))
                         (sr_high (sr_indexes_of r)) /\
                   (&0:int) <= sr_low (sr_indexes_of r) /\
                   sr_low (sr_indexes_of r) <= m /\
                   m < j /\
                   j <= sr_high (sr_indexes_of r) /\
                   sr_high (sr_indexes_of r) <= (&(LENGTH a):int)) /\
                  sr_is_child (SRNode ind l r) l /\
                  sr_is_tree_for
                    l a (sr_low (sr_indexes_of l))
                        (sr_high (sr_indexes_of l)) /\
                  (&0:int) <= sr_low (sr_indexes_of l) /\
                  sr_low (sr_indexes_of l) <= i /\
                  i < m /\
                  m <= sr_high (sr_indexes_of l) /\
                  sr_high (sr_indexes_of l) <= (&(LENGTH a):int))) /\
        (!result:int.
           (?o1:bool.
              (if i = sr_low ind
               then o1 = (if j = sr_high ind then T else F)
               else o1 = F) /\
              (if o1 = T then
                 result = sr_isum ind
               else
                 let m = sr_high (sr_indexes_of l) in
                 if j <= m then
                   result = sr_array_sum a i j
                 else if m <= i then
                   result = sr_array_sum a i j
                 else
                   result =
                     sr_array_sum a i m + sr_array_sum a m j))
           ==> result = sr_array_sum a i j))`;;

let statement =
  `!t:sr_tree. !a:int list. !i:int. !j:int.
     sr_is_tree_for
       t a (sr_low (sr_indexes_of t)) (sr_high (sr_indexes_of t))
     ==> (&0:int) <= sr_low (sr_indexes_of t)
     ==> sr_low (sr_indexes_of t) <= i
     ==> i < j
     ==> j <= sr_high (sr_indexes_of t)
     ==> sr_high (sr_indexes_of t) <= (&(LENGTH a):int)
     ==> sr_query_aux_vc t a i j`;;
