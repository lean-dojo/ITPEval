(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_Harness_harness2qtvc: impossibility of
  reconstructing a binary tree whose left-to-right leaf-depth sequence from
  root depth zero is 1, 3, 2, 2. This file contains no proof.
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

let statement =
  `!x:ntp4vc_tree_reconstruction_tree.
     ~(ntp4vc_tree_reconstruction_depths (&0:int) x =
       CONS (&1:int)
         (CONS (&3:int)
           (CONS (&2:int)
             (CONS (&2:int) []))))`;;
