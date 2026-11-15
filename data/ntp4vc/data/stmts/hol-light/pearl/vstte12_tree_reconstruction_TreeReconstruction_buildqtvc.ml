(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_TreeReconstruction_buildqtvc: the
  top-level verification condition for reconstructing a binary tree from its
  left-to-right leaf-depth list, covering exact reconstruction, a nonempty
  remainder, and total reconstruction failure. This file contains no proof.
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
 `!s1:int list.
    ((!t:ntp4vc_tree_reconstruction_tree.
      !s:int list.
        s1 =
          APPEND
            (ntp4vc_tree_reconstruction_depths (&0:int) t)
            s
        ==>
        if s = [] then
          ntp4vc_tree_reconstruction_depths (&0:int) t = s1
        else
          !t1:ntp4vc_tree_reconstruction_tree.
            ~(ntp4vc_tree_reconstruction_depths (&0:int) t1 = s1)) /\
     ((!t:ntp4vc_tree_reconstruction_tree.
       !s':int list.
         ~(APPEND
             (ntp4vc_tree_reconstruction_depths (&0:int) t)
             s' =
           s1))
      ==>
      !t:ntp4vc_tree_reconstruction_tree.
        ~(ntp4vc_tree_reconstruction_depths (&0:int) t = s1)))`;;
