(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/foveoos11_cm/tree_max_TreeMax_max_auxqtvc: an auxiliary maximum
  verification condition for integer-valued binary trees, using recursive
  membership and upper-bound predicates. This file contains no proof.
*)

let tree_max_aux_tree_INDUCT,tree_max_aux_tree_RECURSION = define_type
  "tree_max_aux_tree =
       TreeMaxAuxNull
     | TreeMaxAuxTree int tree_max_aux_tree tree_max_aux_tree";;

let tree_max_aux_mem =
  new_recursive_definition tree_max_aux_tree_RECURSION
   `(!v:int. tree_max_aux_mem v TreeMaxAuxNull = F) /\
    (!v x:int.
     !l r:tree_max_aux_tree.
       tree_max_aux_mem v (TreeMaxAuxTree x l r) =
       (x = v \/ tree_max_aux_mem v l \/ tree_max_aux_mem v r))`;;

let tree_max_aux_ge_tree =
  new_recursive_definition tree_max_aux_tree_RECURSION
   `(!v:int. tree_max_aux_ge_tree v TreeMaxAuxNull = T) /\
    (!v x:int.
     !l r:tree_max_aux_tree.
       tree_max_aux_ge_tree v (TreeMaxAuxTree x l r) =
       (x <= v /\
        tree_max_aux_ge_tree v l /\
        tree_max_aux_ge_tree v r))`;;

let tree_max_aux_child =
  new_recursive_definition tree_max_aux_tree_RECURSION
   `(!c:tree_max_aux_tree.
       tree_max_aux_child c TreeMaxAuxNull = F) /\
    (!c l r:tree_max_aux_tree.
     !v:int.
       tree_max_aux_child c (TreeMaxAuxTree v l r) =
       (l = c \/ r = c))`;;

let tree_max_aux_int_max = new_definition
 `tree_max_aux_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let tree_max_aux_ready =
  new_recursive_definition tree_max_aux_tree_RECURSION
   `(!acc:int. tree_max_aux_ready TreeMaxAuxNull acc = T) /\
    (!acc v:int.
     !l r:tree_max_aux_tree.
       tree_max_aux_ready (TreeMaxAuxTree v l r) acc =
       (let o1 = tree_max_aux_int_max v acc in
          tree_max_aux_child r (TreeMaxAuxTree v l r) /\
          (!o2:int.
             tree_max_aux_ge_tree o2 r /\
             o1 <= o2 /\
             (o2 = o1 \/ tree_max_aux_mem o2 r)
             ==>
             tree_max_aux_child l (TreeMaxAuxTree v l r))))`;;

let tree_max_aux_result =
  new_recursive_definition tree_max_aux_tree_RECURSION
   `(!result acc:int.
       (tree_max_aux_result result TreeMaxAuxNull acc <=>
        result = acc)) /\
    (!result acc v:int.
     !l r:tree_max_aux_tree.
       (tree_max_aux_result result (TreeMaxAuxTree v l r) acc <=>
        (let o1 = tree_max_aux_int_max v acc in
           ?o2:int.
             (tree_max_aux_ge_tree o2 r /\
              o1 <= o2 /\
              (o2 = o1 \/ tree_max_aux_mem o2 r)) /\
             tree_max_aux_ge_tree result l /\
             o2 <= result /\
             (result = o2 \/ tree_max_aux_mem result l))))`;;

let statement =
 `!t:tree_max_aux_tree.
  !acc:int.
    tree_max_aux_ready t acc /\
    (!result:int.
       tree_max_aux_result result t acc
       ==>
       tree_max_aux_ge_tree result t /\
       acc <= result /\
       (result = acc \/ tree_max_aux_mem result t))`;;
