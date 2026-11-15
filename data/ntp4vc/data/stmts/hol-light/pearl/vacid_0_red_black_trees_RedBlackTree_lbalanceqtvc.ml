(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_RedBlackTree_lbalanceqtvc: the left-balancing
  verification condition for integer-keyed red-black trees, preserving the
  binary-search invariant, black height, and key-value membership. This file
  contains no proof.
*)

let ntp4vc_lbalance_color_INDUCT,ntp4vc_lbalance_color_RECURSION =
  define_type
   "ntp4vc_lbalance_color =
      NTP4VCLBalanceRed
    | NTP4VCLBalanceBlack";;

let ntp4vc_lbalance_tree_INDUCT,ntp4vc_lbalance_tree_RECURSION =
  define_type
   "ntp4vc_lbalance_tree =
      NTP4VCLBalanceLeaf
    | NTP4VCLBalanceNode
        ntp4vc_lbalance_color ntp4vc_lbalance_tree int int
        ntp4vc_lbalance_tree";;

let ntp4vc_lbalance_memt =
  new_recursive_definition ntp4vc_lbalance_tree_RECURSION
   `(!k v:int.
       ntp4vc_lbalance_memt NTP4VCLBalanceLeaf k v <=> F) /\
    (!c:ntp4vc_lbalance_color.
     !l r:ntp4vc_lbalance_tree.
     !k0 v0 k v:int.
       ntp4vc_lbalance_memt
         (NTP4VCLBalanceNode c l k0 v0 r) k v <=>
       (k = k0 /\ v = v0) \/
       ntp4vc_lbalance_memt l k v \/
       ntp4vc_lbalance_memt r k v)`;;

let ntp4vc_lbalance_lt_tree = new_definition
 `ntp4vc_lbalance_lt_tree
    (x:int) (t:ntp4vc_lbalance_tree) <=>
    !k v:int. ntp4vc_lbalance_memt t k v ==> k < x`;;

let ntp4vc_lbalance_gt_tree = new_definition
 `ntp4vc_lbalance_gt_tree
    (x:int) (t:ntp4vc_lbalance_tree) <=>
    !k v:int. ntp4vc_lbalance_memt t k v ==> x < k`;;

let ntp4vc_lbalance_bst =
  new_recursive_definition ntp4vc_lbalance_tree_RECURSION
   `(ntp4vc_lbalance_bst NTP4VCLBalanceLeaf <=> T) /\
    (!c:ntp4vc_lbalance_color.
     !l r:ntp4vc_lbalance_tree.
     !k v:int.
       ntp4vc_lbalance_bst (NTP4VCLBalanceNode c l k v r) <=>
       ntp4vc_lbalance_bst l /\
       ntp4vc_lbalance_bst r /\
       ntp4vc_lbalance_lt_tree k l /\
       ntp4vc_lbalance_gt_tree k r)`;;

let ntp4vc_lbalance_is_not_red =
  new_recursive_definition ntp4vc_lbalance_tree_RECURSION
   `(ntp4vc_lbalance_is_not_red NTP4VCLBalanceLeaf <=> T) /\
    (!c:ntp4vc_lbalance_color.
     !l r:ntp4vc_lbalance_tree.
     !k v:int.
       ntp4vc_lbalance_is_not_red
         (NTP4VCLBalanceNode c l k v r) <=>
       ~(c = NTP4VCLBalanceRed))`;;

let ntp4vc_lbalance_rbtree =
  new_recursive_definition ntp4vc_lbalance_tree_RECURSION
   `(!n:int.
       ntp4vc_lbalance_rbtree n NTP4VCLBalanceLeaf <=>
       n = (&0:int)) /\
    (!n:int.
     !c:ntp4vc_lbalance_color.
     !l r:ntp4vc_lbalance_tree.
     !k v:int.
       ntp4vc_lbalance_rbtree n
         (NTP4VCLBalanceNode c l k v r) <=>
       if c = NTP4VCLBalanceRed then
         ntp4vc_lbalance_rbtree n l /\
         ntp4vc_lbalance_rbtree n r /\
         ntp4vc_lbalance_is_not_red l /\
         ntp4vc_lbalance_is_not_red r
       else
         ntp4vc_lbalance_rbtree (n - (&1:int)) l /\
         ntp4vc_lbalance_rbtree (n - (&1:int)) r)`;;

let ntp4vc_lbalance_almost_rbtree =
  new_recursive_definition ntp4vc_lbalance_tree_RECURSION
   `(!n:int.
       ntp4vc_lbalance_almost_rbtree n NTP4VCLBalanceLeaf <=>
       n = (&0:int)) /\
    (!n:int.
     !c:ntp4vc_lbalance_color.
     !l r:ntp4vc_lbalance_tree.
     !k v:int.
       ntp4vc_lbalance_almost_rbtree n
         (NTP4VCLBalanceNode c l k v r) <=>
       if c = NTP4VCLBalanceRed then
         ntp4vc_lbalance_rbtree n l /\
         ntp4vc_lbalance_rbtree n r
       else
         ntp4vc_lbalance_rbtree (n - (&1:int)) l /\
         ntp4vc_lbalance_rbtree (n - (&1:int)) r)`;;

let ntp4vc_lbalance_left_left_red = new_definition
 `ntp4vc_lbalance_left_left_red (l:ntp4vc_lbalance_tree) <=>
    ?a b c:ntp4vc_lbalance_tree.
    ?kx vx ky vy:int.
      l =
      NTP4VCLBalanceNode NTP4VCLBalanceRed
        (NTP4VCLBalanceNode NTP4VCLBalanceRed a kx vx b)
        ky vy c`;;

let ntp4vc_lbalance_left_right_red = new_definition
 `ntp4vc_lbalance_left_right_red (l:ntp4vc_lbalance_tree) <=>
    ?a b c:ntp4vc_lbalance_tree.
    ?kx vx ky vy:int.
      l =
      NTP4VCLBalanceNode NTP4VCLBalanceRed
        a kx vx
        (NTP4VCLBalanceNode NTP4VCLBalanceRed b ky vy c)`;;

let ntp4vc_lbalance_result = new_definition
 `ntp4vc_lbalance_result
    (l:ntp4vc_lbalance_tree) (k:int) (v:int)
    (r:ntp4vc_lbalance_tree) (result:ntp4vc_lbalance_tree) <=>
    if ntp4vc_lbalance_left_left_red l then
      ?a b c:ntp4vc_lbalance_tree.
      ?kx vx ky vy:int.
        l =
          NTP4VCLBalanceNode NTP4VCLBalanceRed
            (NTP4VCLBalanceNode NTP4VCLBalanceRed a kx vx b)
            ky vy c /\
        result =
          NTP4VCLBalanceNode NTP4VCLBalanceRed
            (NTP4VCLBalanceNode NTP4VCLBalanceBlack a kx vx b)
            ky vy
            (NTP4VCLBalanceNode NTP4VCLBalanceBlack c k v r)
    else if ntp4vc_lbalance_left_right_red l then
      ?a b c:ntp4vc_lbalance_tree.
      ?kx vx ky vy:int.
        l =
          NTP4VCLBalanceNode NTP4VCLBalanceRed
            a kx vx
            (NTP4VCLBalanceNode NTP4VCLBalanceRed b ky vy c) /\
        result =
          NTP4VCLBalanceNode NTP4VCLBalanceRed
            (NTP4VCLBalanceNode NTP4VCLBalanceBlack a kx vx b)
            ky vy
            (NTP4VCLBalanceNode NTP4VCLBalanceBlack c k v r)
    else
      result =
        NTP4VCLBalanceNode NTP4VCLBalanceBlack l k v r`;;

let statement =
 `!k:int.
  !l r:ntp4vc_lbalance_tree.
  !v:int.
    ntp4vc_lbalance_lt_tree k l
    ==>
    ntp4vc_lbalance_gt_tree k r
    ==>
    ntp4vc_lbalance_bst l
    ==>
    ntp4vc_lbalance_bst r
    ==>
    T /\
    (!result:ntp4vc_lbalance_tree.
       ntp4vc_lbalance_result l k v r result
       ==>
       ntp4vc_lbalance_bst result /\
       (!n:int.
          ntp4vc_lbalance_almost_rbtree n l
          ==>
          ntp4vc_lbalance_rbtree n r
          ==>
          ntp4vc_lbalance_rbtree (n + (&1:int)) result) /\
       (!k' v':int.
          ntp4vc_lbalance_memt result k' v' <=>
          if k' = k then v' = v
          else
            ntp4vc_lbalance_memt l k' v' \/
            ntp4vc_lbalance_memt r k' v'))`;;
