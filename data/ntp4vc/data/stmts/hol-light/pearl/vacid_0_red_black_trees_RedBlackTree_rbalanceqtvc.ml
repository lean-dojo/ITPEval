(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_RedBlackTree_rbalanceqtvc: the right-balancing
  verification condition for integer-keyed red-black trees, preserving the
  binary-search invariant, black height, and key-value membership. This file
  contains no proof.
*)

let ntp4vc_rbalance_color_INDUCT,ntp4vc_rbalance_color_RECURSION =
  define_type
   "ntp4vc_rbalance_color =
      NTP4VCRBalanceRed
    | NTP4VCRBalanceBlack";;

let ntp4vc_rbalance_tree_INDUCT,ntp4vc_rbalance_tree_RECURSION =
  define_type
   "ntp4vc_rbalance_tree =
      NTP4VCRBalanceLeaf
    | NTP4VCRBalanceNode
        ntp4vc_rbalance_color ntp4vc_rbalance_tree int int
        ntp4vc_rbalance_tree";;

let ntp4vc_rbalance_memt =
  new_recursive_definition ntp4vc_rbalance_tree_RECURSION
   `(!k v:int.
       ntp4vc_rbalance_memt NTP4VCRBalanceLeaf k v <=> F) /\
    (!c:ntp4vc_rbalance_color.
     !l r:ntp4vc_rbalance_tree.
     !k0 v0 k v:int.
       ntp4vc_rbalance_memt
         (NTP4VCRBalanceNode c l k0 v0 r) k v <=>
       (k = k0 /\ v = v0) \/
       ntp4vc_rbalance_memt l k v \/
       ntp4vc_rbalance_memt r k v)`;;

let ntp4vc_rbalance_lt_tree = new_definition
 `ntp4vc_rbalance_lt_tree
    (x:int) (t:ntp4vc_rbalance_tree) <=>
    !k v:int. ntp4vc_rbalance_memt t k v ==> k < x`;;

let ntp4vc_rbalance_gt_tree = new_definition
 `ntp4vc_rbalance_gt_tree
    (x:int) (t:ntp4vc_rbalance_tree) <=>
    !k v:int. ntp4vc_rbalance_memt t k v ==> x < k`;;

let ntp4vc_rbalance_bst =
  new_recursive_definition ntp4vc_rbalance_tree_RECURSION
   `(ntp4vc_rbalance_bst NTP4VCRBalanceLeaf <=> T) /\
    (!c:ntp4vc_rbalance_color.
     !l r:ntp4vc_rbalance_tree.
     !k v:int.
       ntp4vc_rbalance_bst (NTP4VCRBalanceNode c l k v r) <=>
       ntp4vc_rbalance_bst l /\
       ntp4vc_rbalance_bst r /\
       ntp4vc_rbalance_lt_tree k l /\
       ntp4vc_rbalance_gt_tree k r)`;;

let ntp4vc_rbalance_is_not_red =
  new_recursive_definition ntp4vc_rbalance_tree_RECURSION
   `(ntp4vc_rbalance_is_not_red NTP4VCRBalanceLeaf <=> T) /\
    (!c:ntp4vc_rbalance_color.
     !l r:ntp4vc_rbalance_tree.
     !k v:int.
       ntp4vc_rbalance_is_not_red
         (NTP4VCRBalanceNode c l k v r) <=>
       ~(c = NTP4VCRBalanceRed))`;;

let ntp4vc_rbalance_rbtree =
  new_recursive_definition ntp4vc_rbalance_tree_RECURSION
   `(!n:int.
       ntp4vc_rbalance_rbtree n NTP4VCRBalanceLeaf <=>
       n = (&0:int)) /\
    (!n:int.
     !c:ntp4vc_rbalance_color.
     !l r:ntp4vc_rbalance_tree.
     !k v:int.
       ntp4vc_rbalance_rbtree n
         (NTP4VCRBalanceNode c l k v r) <=>
       if c = NTP4VCRBalanceRed then
         ntp4vc_rbalance_rbtree n l /\
         ntp4vc_rbalance_rbtree n r /\
         ntp4vc_rbalance_is_not_red l /\
         ntp4vc_rbalance_is_not_red r
       else
         ntp4vc_rbalance_rbtree (n - (&1:int)) l /\
         ntp4vc_rbalance_rbtree (n - (&1:int)) r)`;;

let ntp4vc_rbalance_almost_rbtree =
  new_recursive_definition ntp4vc_rbalance_tree_RECURSION
   `(!n:int.
       ntp4vc_rbalance_almost_rbtree n NTP4VCRBalanceLeaf <=>
       n = (&0:int)) /\
    (!n:int.
     !c:ntp4vc_rbalance_color.
     !l r:ntp4vc_rbalance_tree.
     !k v:int.
       ntp4vc_rbalance_almost_rbtree n
         (NTP4VCRBalanceNode c l k v r) <=>
       if c = NTP4VCRBalanceRed then
         ntp4vc_rbalance_rbtree n l /\
         ntp4vc_rbalance_rbtree n r
       else
         ntp4vc_rbalance_rbtree (n - (&1:int)) l /\
         ntp4vc_rbalance_rbtree (n - (&1:int)) r)`;;

let ntp4vc_rbalance_right_left_red = new_definition
 `ntp4vc_rbalance_right_left_red (r:ntp4vc_rbalance_tree) <=>
    ?b c d:ntp4vc_rbalance_tree.
    ?ky vy kz vz:int.
      r =
      NTP4VCRBalanceNode NTP4VCRBalanceRed
        (NTP4VCRBalanceNode NTP4VCRBalanceRed b ky vy c)
        kz vz d`;;

let ntp4vc_rbalance_right_right_red = new_definition
 `ntp4vc_rbalance_right_right_red (r:ntp4vc_rbalance_tree) <=>
    ?b c d:ntp4vc_rbalance_tree.
    ?ky vy kz vz:int.
      r =
      NTP4VCRBalanceNode NTP4VCRBalanceRed
        b ky vy
        (NTP4VCRBalanceNode NTP4VCRBalanceRed c kz vz d)`;;

let ntp4vc_rbalance_result = new_definition
 `ntp4vc_rbalance_result
    (l:ntp4vc_rbalance_tree) (k:int) (v:int)
    (r:ntp4vc_rbalance_tree) (result:ntp4vc_rbalance_tree) <=>
    if ntp4vc_rbalance_right_left_red r then
      ?b c d:ntp4vc_rbalance_tree.
      ?ky vy kz vz:int.
        r =
          NTP4VCRBalanceNode NTP4VCRBalanceRed
            (NTP4VCRBalanceNode NTP4VCRBalanceRed b ky vy c)
            kz vz d /\
        result =
          NTP4VCRBalanceNode NTP4VCRBalanceRed
            (NTP4VCRBalanceNode NTP4VCRBalanceBlack l k v b)
            ky vy
            (NTP4VCRBalanceNode NTP4VCRBalanceBlack c kz vz d)
    else if ntp4vc_rbalance_right_right_red r then
      ?b c d:ntp4vc_rbalance_tree.
      ?ky vy kz vz:int.
        r =
          NTP4VCRBalanceNode NTP4VCRBalanceRed
            b ky vy
            (NTP4VCRBalanceNode NTP4VCRBalanceRed c kz vz d) /\
        result =
          NTP4VCRBalanceNode NTP4VCRBalanceRed
            (NTP4VCRBalanceNode NTP4VCRBalanceBlack l k v b)
            ky vy
            (NTP4VCRBalanceNode NTP4VCRBalanceBlack c kz vz d)
    else
      result =
        NTP4VCRBalanceNode NTP4VCRBalanceBlack l k v r`;;

let statement =
 `!k:int.
  !l r:ntp4vc_rbalance_tree.
  !v:int.
    ntp4vc_rbalance_lt_tree k l
    ==>
    ntp4vc_rbalance_gt_tree k r
    ==>
    ntp4vc_rbalance_bst l
    ==>
    ntp4vc_rbalance_bst r
    ==>
    T /\
    (!result:ntp4vc_rbalance_tree.
       ntp4vc_rbalance_result l k v r result
       ==>
       ntp4vc_rbalance_bst result /\
       (!n:int.
          ntp4vc_rbalance_almost_rbtree n r
          ==>
          ntp4vc_rbalance_rbtree n l
          ==>
          ntp4vc_rbalance_rbtree (n + (&1:int)) result) /\
       (!k' v':int.
          ntp4vc_rbalance_memt result k' v' <=>
          if k' = k then v' = v
          else
            ntp4vc_rbalance_memt l k' v' \/
            ntp4vc_rbalance_memt r k' v'))`;;
