(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_extractqtvc: a Braun-heap extraction
  verification condition preserving heap order, the Braun size invariant,
  element multiplicities, and total size. This file contains no proof.
*)

let braun_extract_tree_INDUCT,braun_extract_tree_RECURSION = define_type
  "braun_extract_tree =
       BraunExtractEmpty
     | BraunExtractNode braun_extract_tree A braun_extract_tree";;

let braun_extract_size =
  new_recursive_definition braun_extract_tree_RECURSION
   `(braun_extract_size (BraunExtractEmpty:A braun_extract_tree) =
       (&0:int)) /\
    (!l x r.
       braun_extract_size (BraunExtractNode l x r) =
       (&1:int) + braun_extract_size l + braun_extract_size r)`;;

let braun_extract_occ =
  new_recursive_definition braun_extract_tree_RECURSION
   `(!x:A.
       braun_extract_occ x BraunExtractEmpty = (&0:int)) /\
    (!x y:A.
     !l r:A braun_extract_tree.
       braun_extract_occ x (BraunExtractNode l y r) =
       (if y = x then (&1:int) else (&0:int)) +
       braun_extract_occ x l + braun_extract_occ x r)`;;

let braun_extract_le_root =
  new_recursive_definition braun_extract_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
       braun_extract_le_root le e BraunExtractEmpty = T) /\
    (!le:A->A->bool.
     !e x:A.
     !l r:A braun_extract_tree.
       braun_extract_le_root le e (BraunExtractNode l x r) = le e x)`;;

let braun_extract_heap =
  new_recursive_definition braun_extract_tree_RECURSION
   `(!le:A->A->bool.
       braun_extract_heap le BraunExtractEmpty = T) /\
    (!le:A->A->bool.
     !x:A.
     !l r:A braun_extract_tree.
       braun_extract_heap le (BraunExtractNode l x r) =
       (braun_extract_le_root le x l /\
        braun_extract_heap le l /\
        braun_extract_le_root le x r /\
        braun_extract_heap le r))`;;

let braun_extract_inv =
  new_recursive_definition braun_extract_tree_RECURSION
   `(braun_extract_inv (BraunExtractEmpty:A braun_extract_tree) = T) /\
    (!x:A.
     !l r:A braun_extract_tree.
       braun_extract_inv (BraunExtractNode l x r) =
       ((braun_extract_size l = braun_extract_size r \/
         braun_extract_size l =
           braun_extract_size r + (&1:int)) /\
        braun_extract_inv l /\
        braun_extract_inv r))`;;

let braun_extract_is_child =
  new_recursive_definition braun_extract_tree_RECURSION
   `(!q:A braun_extract_tree.
       braun_extract_is_child BraunExtractEmpty q = F) /\
    (!x:A.
     !l r q:A braun_extract_tree.
       braun_extract_is_child (BraunExtractNode l x r) q =
       (l = q \/ r = q))`;;

let braun_extract_ready =
  new_recursive_definition braun_extract_tree_RECURSION
   `(!le:A->A->bool.
       braun_extract_ready le BraunExtractEmpty = F) /\
    (!le:A->A->bool.
     !y:A.
     !l r:A braun_extract_tree.
       braun_extract_ready le (BraunExtractNode l y r) =
       (if l = BraunExtractEmpty then T
        else
          braun_extract_is_child (BraunExtractNode l y r) l /\
          braun_extract_heap le l /\
          braun_extract_inv l /\
          (&0:int) < braun_extract_size l))`;;

let braun_extract_step =
  new_recursive_definition braun_extract_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
     !result:A braun_extract_tree.
       braun_extract_step le e result BraunExtractEmpty = F) /\
    (!le:A->A->bool.
     !e y:A.
     !l r result:A braun_extract_tree.
       braun_extract_step le e result (BraunExtractNode l y r) =
       (if l = BraunExtractEmpty then
          e = y /\ result = BraunExtractEmpty
        else
          ?recursive_result:A braun_extract_tree.
            (braun_extract_heap le recursive_result /\
             braun_extract_inv recursive_result /\
             braun_extract_size recursive_result =
               braun_extract_size l - (&1:int) /\
             braun_extract_occ e recursive_result =
               braun_extract_occ e l - (&1:int) /\
             (!x:A.
                ~(x = e)
                ==> braun_extract_occ x recursive_result =
                    braun_extract_occ x l)) /\
            result = BraunExtractNode r y recursive_result))`;;

let statement =
 `!le:A->A->bool.
  !t:A braun_extract_tree.
    ((!x:A. le x x) /\
     (!x y z:A. le x y /\ le y z ==> le x z) /\
     (!x y:A. le x y \/ le y x))
    ==>
    braun_extract_heap le t
    ==>
    braun_extract_inv t
    ==>
    (&0:int) < braun_extract_size t
    ==>
    braun_extract_ready le t /\
    (!e:A.
     !result:A braun_extract_tree.
       braun_extract_step le e result t
       ==>
       braun_extract_heap le result /\
       braun_extract_inv result /\
       braun_extract_size result =
         braun_extract_size t - (&1:int) /\
       braun_extract_occ e result =
         braun_extract_occ e t - (&1:int) /\
       (!x:A.
          ~(x = e)
          ==> braun_extract_occ x result = braun_extract_occ x t))`;;
