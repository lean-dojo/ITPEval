(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_ZipperBased_buildqtvc: the initialization
  verification condition for zipper-based reconstruction of a binary tree
  from its left-to-right leaf-depth list. This file contains no proof.
*)

let ntp4vc_tree_reconstruction_tree_INDUCT,
    ntp4vc_tree_reconstruction_tree_RECURSION =
  define_type
   "ntp4vc_tree_reconstruction_tree =
        NTP4VC_TREE_RECONSTRUCTION_LEAF
      | NTP4VC_TREE_RECONSTRUCTION_NODE
          ntp4vc_tree_reconstruction_tree
          ntp4vc_tree_reconstruction_tree";;

let ntp4vc_tree_reconstruction_depths =
  new_recursive_definition ntp4vc_tree_reconstruction_tree_RECURSION
   `(!d:int.
       ntp4vc_tree_reconstruction_depths
         d NTP4VC_TREE_RECONSTRUCTION_LEAF =
       CONS d []) /\
    (!d:int.
     !l r:ntp4vc_tree_reconstruction_tree.
       ntp4vc_tree_reconstruction_depths
         d (NTP4VC_TREE_RECONSTRUCTION_NODE l r) =
       APPEND
         (ntp4vc_tree_reconstruction_depths (d + (&1:int)) l)
         (ntp4vc_tree_reconstruction_depths (d + (&1:int)) r))`;;

let ntp4vc_tree_reconstruction_forest_depths =
  new_recursive_definition list_RECURSION
   `(ntp4vc_tree_reconstruction_forest_depths
       ([]:(int#ntp4vc_tree_reconstruction_tree) list) = []) /\
    (!p:int#ntp4vc_tree_reconstruction_tree.
     !r:(int#ntp4vc_tree_reconstruction_tree) list.
       ntp4vc_tree_reconstruction_forest_depths (CONS p r) =
       APPEND
         (ntp4vc_tree_reconstruction_depths (FST p) (SND p))
         (ntp4vc_tree_reconstruction_forest_depths r))`;;

let ntp4vc_tree_reconstruction_greedy =
  new_recursive_definition ntp4vc_tree_reconstruction_tree_RECURSION
   `(!d d1:int.
       ntp4vc_tree_reconstruction_greedy
         d d1 NTP4VC_TREE_RECONSTRUCTION_LEAF =
       (~(d = d1) /\ T)) /\
    (!d d1:int.
     !l r:ntp4vc_tree_reconstruction_tree.
       ntp4vc_tree_reconstruction_greedy
         d d1 (NTP4VC_TREE_RECONSTRUCTION_NODE l r) =
       (~(d = d1) /\
        ntp4vc_tree_reconstruction_greedy d (d1 + (&1:int)) l))`;;

let ntp4vc_tree_reconstruction_g_RULES,
    ntp4vc_tree_reconstruction_g_INDUCT,
    ntp4vc_tree_reconstruction_g_CASES =
  new_inductive_definition
   `(ntp4vc_tree_reconstruction_g
       ([]:(int#ntp4vc_tree_reconstruction_tree) list)) /\
    (!d:int.
     !t:ntp4vc_tree_reconstruction_tree.
       ntp4vc_tree_reconstruction_g (CONS (d,t) [])) /\
    (!d1 d2:int.
     !t2 t1:ntp4vc_tree_reconstruction_tree.
     !l:(int#ntp4vc_tree_reconstruction_tree) list.
       ntp4vc_tree_reconstruction_greedy d1 d2 t2 /\
       ntp4vc_tree_reconstruction_g (CONS (d1,t1) l)
       ==>
       ntp4vc_tree_reconstruction_g
         (CONS (d2,t2) (CONS (d1,t1) l)))`;;

let ntp4vc_tree_reconstruction_only_leaf =
  new_recursive_definition list_RECURSION
   `(ntp4vc_tree_reconstruction_only_leaf
       ([]:(int#ntp4vc_tree_reconstruction_tree) list) = T) /\
    (!p:int#ntp4vc_tree_reconstruction_tree.
     !r:(int#ntp4vc_tree_reconstruction_tree) list.
       ntp4vc_tree_reconstruction_only_leaf (CONS p r) =
       (SND p = NTP4VC_TREE_RECONSTRUCTION_LEAF /\
        ntp4vc_tree_reconstruction_only_leaf r))`;;

let ntp4vc_tree_reconstruction_map_leaf =
  new_recursive_definition list_RECURSION
   `(ntp4vc_tree_reconstruction_map_leaf ([]:int list) =
       ([]:(int#ntp4vc_tree_reconstruction_tree) list)) /\
    (!d:int.
     !r:int list.
       ntp4vc_tree_reconstruction_map_leaf (CONS d r) =
       CONS
         (d,NTP4VC_TREE_RECONSTRUCTION_LEAF)
         (ntp4vc_tree_reconstruction_map_leaf r))`;;

let ntp4vc_tree_reconstruction_head_invariant =
  new_recursive_definition ntp4vc_tree_reconstruction_tree_RECURSION
   `(!d:int.
     !left:(int#ntp4vc_tree_reconstruction_tree) list.
       ntp4vc_tree_reconstruction_head_invariant
         d NTP4VC_TREE_RECONSTRUCTION_LEAF left = T) /\
    (!d:int.
     !l r:ntp4vc_tree_reconstruction_tree.
     !left:(int#ntp4vc_tree_reconstruction_tree) list.
       ntp4vc_tree_reconstruction_head_invariant
         d (NTP4VC_TREE_RECONSTRUCTION_NODE l r) left =
       ntp4vc_tree_reconstruction_g
         (CONS (d + (&1:int),l) left))`;;

let ntp4vc_tree_reconstruction_right_invariant =
  new_recursive_definition list_RECURSION
   `(!left:(int#ntp4vc_tree_reconstruction_tree) list.
       ntp4vc_tree_reconstruction_right_invariant
         left ([]:(int#ntp4vc_tree_reconstruction_tree) list) = T) /\
    (!left:(int#ntp4vc_tree_reconstruction_tree) list.
     !p:int#ntp4vc_tree_reconstruction_tree.
     !right:(int#ntp4vc_tree_reconstruction_tree) list.
       ntp4vc_tree_reconstruction_right_invariant
         left (CONS p right) =
       (ntp4vc_tree_reconstruction_only_leaf right /\
        ntp4vc_tree_reconstruction_head_invariant
          (FST p) (SND p) left))`;;

let statement =
  `!s:int list.
     let o1 = ntp4vc_tree_reconstruction_map_leaf s in
     let o2 = ([]:(int#ntp4vc_tree_reconstruction_tree) list) in
       (ntp4vc_tree_reconstruction_g o2 /\
        ntp4vc_tree_reconstruction_right_invariant o2 o1) /\
       (!result:ntp4vc_tree_reconstruction_tree.
          ntp4vc_tree_reconstruction_depths (&0:int) result =
            ntp4vc_tree_reconstruction_forest_depths
              (APPEND (REVERSE o2) o1)
          ==>
          ntp4vc_tree_reconstruction_depths (&0:int) result = s) /\
       ((!t:ntp4vc_tree_reconstruction_tree.
           ~(ntp4vc_tree_reconstruction_depths (&0:int) t =
             ntp4vc_tree_reconstruction_forest_depths
               (APPEND (REVERSE o2) o1)))
        ==>
        !t:ntp4vc_tree_reconstruction_tree.
          ~(ntp4vc_tree_reconstruction_depths (&0:int) t = s))`;;
