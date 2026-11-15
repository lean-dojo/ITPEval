(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/foveoos11_challenge2_MaximumTree_maximumqtvc: a maximum-of-binary-tree
  verification condition covering recursive size decrease and the
  characterization of a greatest stored integer. This file contains no proof.
*)

let maximum_tree_INDUCT,maximum_tree_RECURSION = define_type
  "maximum_tree =
       MaximumTreeEmpty
     | MaximumTreeNode maximum_tree int maximum_tree";;

let maximum_tree_size =
  new_recursive_definition maximum_tree_RECURSION
   `(maximum_tree_size MaximumTreeEmpty = (&0:int)) /\
    (!l r:maximum_tree.
     !v:int.
       maximum_tree_size (MaximumTreeNode l v r) =
       (&1:int) + maximum_tree_size l + maximum_tree_size r)`;;

let maximum_tree_mem =
  new_recursive_definition maximum_tree_RECURSION
   `(!x:int. maximum_tree_mem x MaximumTreeEmpty = F) /\
    (!x v:int.
     !l r:maximum_tree.
       maximum_tree_mem x (MaximumTreeNode l v r) =
       (maximum_tree_mem x l \/ x = v \/ maximum_tree_mem x r))`;;

let maximum_tree_int_max = new_definition
  `maximum_tree_int_max (x:int) (y:int) =
     if x <= y then y else x`;;

let maximum_tree_decrease = new_definition
 `maximum_tree_decrease (t:maximum_tree) <=>
    (?v:int.
       t = MaximumTreeNode MaximumTreeEmpty v MaximumTreeEmpty) \/
    (?v:int.
     ?s:maximum_tree.
       t = MaximumTreeNode MaximumTreeEmpty v s /\
       (((&0:int) <= maximum_tree_size t /\
         maximum_tree_size s < maximum_tree_size t) /\
        ~(s = MaximumTreeEmpty))) \/
    (?s:maximum_tree.
     ?v:int.
       t = MaximumTreeNode s v MaximumTreeEmpty /\
       (((&0:int) <= maximum_tree_size t /\
         maximum_tree_size s < maximum_tree_size t) /\
        ~(s = MaximumTreeEmpty))) \/
    (?l r:maximum_tree.
     ?v:int.
       t = MaximumTreeNode l v r /\
       ~(l = MaximumTreeEmpty) /\
       ~(r = MaximumTreeEmpty) /\
       ((((&0:int) <= maximum_tree_size t /\
          maximum_tree_size r < maximum_tree_size t) /\
         ~(r = MaximumTreeEmpty)) /\
        (!o1:int.
           maximum_tree_mem o1 r /\
           (!x:int. maximum_tree_mem x r ==> x <= o1)
           ==>
           (((&0:int) <= maximum_tree_size t /\
             maximum_tree_size l < maximum_tree_size t) /\
            ~(l = MaximumTreeEmpty)))))`;;

let maximum_tree_result = new_definition
 `maximum_tree_result (result:int) (t:maximum_tree) <=>
    (?v:int.
       t = MaximumTreeNode MaximumTreeEmpty v MaximumTreeEmpty /\
       result = v) \/
    (?v:int.
     ?s:maximum_tree.
       t = MaximumTreeNode MaximumTreeEmpty v s /\
       ~(s = MaximumTreeEmpty) /\
       (?o1:int.
          (maximum_tree_mem o1 s /\
           (!x:int. maximum_tree_mem x s ==> x <= o1)) /\
          result = maximum_tree_int_max o1 v)) \/
    (?s:maximum_tree.
     ?v:int.
       t = MaximumTreeNode s v MaximumTreeEmpty /\
       ~(s = MaximumTreeEmpty) /\
       (?o1:int.
          (maximum_tree_mem o1 s /\
           (!x:int. maximum_tree_mem x s ==> x <= o1)) /\
          result = maximum_tree_int_max o1 v)) \/
    (?l r:maximum_tree.
     ?v:int.
       t = MaximumTreeNode l v r /\
       ~(l = MaximumTreeEmpty) /\
       ~(r = MaximumTreeEmpty) /\
       (?o1:int.
          (maximum_tree_mem o1 r /\
           (!x:int. maximum_tree_mem x r ==> x <= o1)) /\
          (?o2:int.
             (maximum_tree_mem o2 l /\
              (!x:int. maximum_tree_mem x l ==> x <= o2)) /\
             result =
               maximum_tree_int_max
                 o2 (maximum_tree_int_max v o1))))`;;

let statement =
 `!t:maximum_tree.
    ~(t = MaximumTreeEmpty)
    ==>
    maximum_tree_decrease t /\
    (!result:int.
       maximum_tree_result result t
       ==>
       maximum_tree_mem result t /\
       (!x:int. maximum_tree_mem x t ==> x <= result))`;;
