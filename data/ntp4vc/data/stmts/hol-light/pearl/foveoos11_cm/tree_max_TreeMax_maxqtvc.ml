(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/foveoos11_cm/tree_max_TreeMax_maxqtvc: the verification condition for
  combining right- and left-subtree maxima into a maximum integer of a
  nonempty binary tree. This file contains no proof.
*)

let tree_max_tree_INDUCT,tree_max_tree_RECURSION = define_type
  "tree_max_tree =
       TreeMaxNull
     | TreeMaxTree int tree_max_tree tree_max_tree";;

let tree_max_mem =
  new_recursive_definition tree_max_tree_RECURSION
   `(!v:int. tree_max_mem v TreeMaxNull = F) /\
    (!v x:int.
     !l r:tree_max_tree.
       tree_max_mem v (TreeMaxTree x l r) =
       (x = v \/ tree_max_mem v l \/ tree_max_mem v r))`;;

let tree_max_ge_tree =
  new_recursive_definition tree_max_tree_RECURSION
   `(!v:int. tree_max_ge_tree v TreeMaxNull = T) /\
    (!v x:int.
     !l r:tree_max_tree.
       tree_max_ge_tree v (TreeMaxTree x l r) =
       (x <= v /\
        tree_max_ge_tree v l /\
        tree_max_ge_tree v r))`;;

let tree_max_branch_condition =
  new_recursive_definition tree_max_tree_RECURSION
   `(tree_max_branch_condition TreeMaxNull = F) /\
    (!v:int.
     !l r:tree_max_tree.
       tree_max_branch_condition (TreeMaxTree v l r) = T)`;;

let tree_max_result_premise =
  new_recursive_definition tree_max_tree_RECURSION
   `(!result:int.
       tree_max_result_premise TreeMaxNull result = F) /\
    (!result v:int.
     !l r:tree_max_tree.
       tree_max_result_premise (TreeMaxTree v l r) result =
       (?o1:int.
          (tree_max_ge_tree o1 r /\
           v <= o1 /\
           (o1 = v \/ tree_max_mem o1 r)) /\
          tree_max_ge_tree result l /\
          o1 <= result /\
          (result = o1 \/ tree_max_mem result l)))`;;

let statement =
 `!t:tree_max_tree.
    ~(t = TreeMaxNull)
    ==>
    tree_max_branch_condition t /\
    (!result:int.
       tree_max_result_premise t result
       ==>
       tree_max_ge_tree result t /\
       tree_max_mem result t)`;;
