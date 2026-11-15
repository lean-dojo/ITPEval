(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vstte12_tree_reconstruction_TreeReconstruction_build_recqtvc: the
  recursive verification condition for reconstructing a binary tree from its
  left-to-right leaf-depth list, including termination decrease, successful
  reconstruction, and failure propagation. This file contains no proof.
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
 `!s:int list.
  !d:int.
    if s = [] then
      !t:ntp4vc_tree_reconstruction_tree.
      !s':int list.
        ~(APPEND (ntp4vc_tree_reconstruction_depths d t) s' = s)
    else
      let h = HD s in
      let t = TL s in
      if h < d then
        !t1:ntp4vc_tree_reconstruction_tree.
        !s':int list.
          ~(APPEND (ntp4vc_tree_reconstruction_depths d t1) s' = s)
      else if h = d then
        s =
          APPEND
            (ntp4vc_tree_reconstruction_depths
              d NTP4VC_TREE_RECONSTRUCTION_LEAF)
            t
      else
        let o1 = d + (&1:int) in
        ((&0:int) <= HD s - d /\
         HD s - o1 < HD s - d) /\
        (!l:ntp4vc_tree_reconstruction_tree.
         !s1:int list.
           s =
             APPEND
               (ntp4vc_tree_reconstruction_depths o1 l) s1
           ==>
           let o2 = d + (&1:int) in
           (((&0:int) <= (&(LENGTH s):int) /\
             LENGTH s1 < LENGTH s) \/
            (LENGTH s = LENGTH s1 /\
             (&0:int) <= HD s - d /\
             HD s1 - o2 < HD s - d)) /\
           (!r:ntp4vc_tree_reconstruction_tree.
            !s2:int list.
              s1 =
                APPEND
                  (ntp4vc_tree_reconstruction_depths o2 r) s2
              ==>
              s =
                APPEND
                  (ntp4vc_tree_reconstruction_depths d
                    (NTP4VC_TREE_RECONSTRUCTION_NODE l r))
                  s2) /\
           ((!t1:ntp4vc_tree_reconstruction_tree.
             !s':int list.
               ~(APPEND
                   (ntp4vc_tree_reconstruction_depths o2 t1)
                   s' =
                 s1))
            ==>
            (!t1:ntp4vc_tree_reconstruction_tree.
             !s':int list.
               ~(APPEND
                   (ntp4vc_tree_reconstruction_depths d t1)
                   s' =
                 s)))) /\
        ((!t1:ntp4vc_tree_reconstruction_tree.
          !s':int list.
            ~(APPEND
                (ntp4vc_tree_reconstruction_depths o1 t1)
                s' =
              s))
         ==>
         (!t1:ntp4vc_tree_reconstruction_tree.
          !s':int list.
            ~(APPEND
                (ntp4vc_tree_reconstruction_depths d t1)
                s' =
              s)))`;;
