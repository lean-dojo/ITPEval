(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_fast_sizeqtvc: a Braun-tree fast-size
  verification condition relating the recursive balance invariant and the
  arithmetic result specification to the tree's size. This file contains no
  proof.
*)

let braun_fast_size_tree_INDUCT,braun_fast_size_tree_RECURSION =
  define_type
    "braun_fast_size_tree =
       BraunFastSizeEmpty
     | BraunFastSizeNode braun_fast_size_tree A braun_fast_size_tree";;

let braun_fast_size =
  new_recursive_definition braun_fast_size_tree_RECURSION
   `(braun_fast_size (BraunFastSizeEmpty:A braun_fast_size_tree) =
       (&0:int)) /\
    (!l x r.
       braun_fast_size (BraunFastSizeNode l x r) =
       (&1:int) + braun_fast_size l + braun_fast_size r)`;;

let braun_fast_size_inv =
  new_recursive_definition braun_fast_size_tree_RECURSION
   `(braun_fast_size_inv
       (BraunFastSizeEmpty:A braun_fast_size_tree) = T) /\
    (!x:A.
     !l r:A braun_fast_size_tree.
       braun_fast_size_inv (BraunFastSizeNode l x r) =
       ((braun_fast_size l = braun_fast_size r \/
         braun_fast_size l = braun_fast_size r + (&1:int)) /\
        braun_fast_size_inv l /\
        braun_fast_size_inv r))`;;

let braun_fast_size_branch =
  new_recursive_definition braun_fast_size_tree_RECURSION
   `(braun_fast_size_branch
       (BraunFastSizeEmpty:A braun_fast_size_tree) = T) /\
    (!x:A.
     !l r:A braun_fast_size_tree.
       braun_fast_size_branch (BraunFastSizeNode l x r) =
       (((l = r \/ r = r) /\ braun_fast_size_inv r) /\
        braun_fast_size_inv l /\
        (&0:int) <= braun_fast_size r /\
        braun_fast_size r <= braun_fast_size l /\
        braun_fast_size l <= braun_fast_size r + (&1:int)))`;;

let braun_fast_size_result =
  new_recursive_definition braun_fast_size_tree_RECURSION
   `(!result:int.
       braun_fast_size_result result BraunFastSizeEmpty =
       (result = (&0:int))) /\
    (!result:int.
     !x:A.
     !l r:A braun_fast_size_tree.
       braun_fast_size_result result (BraunFastSizeNode l x r) =
       (?o1:int.
          braun_fast_size l = braun_fast_size r + o1 /\
          result =
            (&1:int) + (&2:int) * braun_fast_size r + o1))`;;

let statement =
 `!t:A braun_fast_size_tree.
    braun_fast_size_inv t
    ==>
    braun_fast_size_branch t /\
    (!result:int.
       braun_fast_size_result result t
       ==>
       result = braun_fast_size t)`;;
