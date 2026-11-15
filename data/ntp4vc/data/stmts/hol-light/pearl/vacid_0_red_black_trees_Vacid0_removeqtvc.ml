(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_Vacid0_removeqtvc: the remove verification
  condition for an integer-keyed red-black-tree map with a default value,
  preserving its invariant and universally quantified membership update.
  This file contains no proof.
*)

let ntp4vc_vacid_remove_color_INDUCT,
    ntp4vc_vacid_remove_color_RECURSION =
  define_type
   "ntp4vc_vacid_remove_color =
      NTP4VCVacidRemoveRed
    | NTP4VCVacidRemoveBlack";;

let ntp4vc_vacid_remove_tree_INDUCT,
    ntp4vc_vacid_remove_tree_RECURSION =
  define_type
   "ntp4vc_vacid_remove_tree =
      NTP4VCVacidRemoveLeaf
    | NTP4VCVacidRemoveNode
        ntp4vc_vacid_remove_color ntp4vc_vacid_remove_tree int int
        ntp4vc_vacid_remove_tree";;

let ntp4vc_vacid_remove_memt =
  new_recursive_definition ntp4vc_vacid_remove_tree_RECURSION
   `(!k v:int.
       ntp4vc_vacid_remove_memt NTP4VCVacidRemoveLeaf k v <=> F) /\
    (!c:ntp4vc_vacid_remove_color.
     !l r:ntp4vc_vacid_remove_tree.
     !k0 v0 k v:int.
       ntp4vc_vacid_remove_memt
         (NTP4VCVacidRemoveNode c l k0 v0 r) k v <=>
       (k = k0 /\ v = v0) \/
       ntp4vc_vacid_remove_memt l k v \/
       ntp4vc_vacid_remove_memt r k v)`;;

let ntp4vc_vacid_remove_lt_tree = new_definition
 `ntp4vc_vacid_remove_lt_tree
    (x:int) (t:ntp4vc_vacid_remove_tree) <=>
    !k v:int. ntp4vc_vacid_remove_memt t k v ==> k < x`;;

let ntp4vc_vacid_remove_gt_tree = new_definition
 `ntp4vc_vacid_remove_gt_tree
    (x:int) (t:ntp4vc_vacid_remove_tree) <=>
    !k v:int. ntp4vc_vacid_remove_memt t k v ==> x < k`;;

let ntp4vc_vacid_remove_bst =
  new_recursive_definition ntp4vc_vacid_remove_tree_RECURSION
   `(ntp4vc_vacid_remove_bst NTP4VCVacidRemoveLeaf <=> T) /\
    (!c:ntp4vc_vacid_remove_color.
     !l r:ntp4vc_vacid_remove_tree.
     !k v:int.
       ntp4vc_vacid_remove_bst
         (NTP4VCVacidRemoveNode c l k v r) <=>
       ntp4vc_vacid_remove_bst l /\
       ntp4vc_vacid_remove_bst r /\
       ntp4vc_vacid_remove_lt_tree k l /\
       ntp4vc_vacid_remove_gt_tree k r)`;;

let ntp4vc_vacid_remove_is_not_red =
  new_recursive_definition ntp4vc_vacid_remove_tree_RECURSION
   `(ntp4vc_vacid_remove_is_not_red NTP4VCVacidRemoveLeaf <=> T) /\
    (!c:ntp4vc_vacid_remove_color.
     !l r:ntp4vc_vacid_remove_tree.
     !k v:int.
       ntp4vc_vacid_remove_is_not_red
         (NTP4VCVacidRemoveNode c l k v r) <=>
       ~(c = NTP4VCVacidRemoveRed))`;;

let ntp4vc_vacid_remove_rbtree =
  new_recursive_definition ntp4vc_vacid_remove_tree_RECURSION
   `(!n:int.
       ntp4vc_vacid_remove_rbtree n NTP4VCVacidRemoveLeaf <=>
       n = (&0:int)) /\
    (!n:int.
     !c:ntp4vc_vacid_remove_color.
     !l r:ntp4vc_vacid_remove_tree.
     !k v:int.
       ntp4vc_vacid_remove_rbtree n
         (NTP4VCVacidRemoveNode c l k v r) <=>
       if c = NTP4VCVacidRemoveRed then
         ntp4vc_vacid_remove_rbtree n l /\
         ntp4vc_vacid_remove_rbtree n r /\
         ntp4vc_vacid_remove_is_not_red l /\
         ntp4vc_vacid_remove_is_not_red r
       else
         ntp4vc_vacid_remove_rbtree (n - (&1:int)) l /\
         ntp4vc_vacid_remove_rbtree (n - (&1:int)) r)`;;

let ntp4vc_vacid_remove_inv = new_definition
 `ntp4vc_vacid_remove_inv
    (state:int#ntp4vc_vacid_remove_tree) <=>
    ntp4vc_vacid_remove_bst (SND state) /\
    (?n:int. ntp4vc_vacid_remove_rbtree n (SND state))`;;

let ntp4vc_vacid_remove_default = new_definition
 `ntp4vc_vacid_remove_default
    (state:int#ntp4vc_vacid_remove_tree) =
    FST state`;;

let ntp4vc_vacid_remove_mem = new_definition
 `ntp4vc_vacid_remove_mem
    (state:int#ntp4vc_vacid_remove_tree) (k:int) (v:int) <=>
    ntp4vc_vacid_remove_memt (SND state) k v \/
    (v = ntp4vc_vacid_remove_default state /\
     (!v':int.
        ~ntp4vc_vacid_remove_memt (SND state) k v'))`;;

let ntp4vc_vacid_remove_post = new_definition
 `ntp4vc_vacid_remove_post
    (m:int) (m1:ntp4vc_vacid_remove_tree) (k:int)
    (m2:ntp4vc_vacid_remove_tree) <=>
    ntp4vc_vacid_remove_inv (m,m2) /\
    (!k' v':int.
       ntp4vc_vacid_remove_mem (m,m2) k' v' <=>
       if k' = k then v' = m
       else ntp4vc_vacid_remove_mem (m,m1) k' v')`;;

let statement =
 `!m:int.
  !m1:ntp4vc_vacid_remove_tree.
  !k:int.
    ntp4vc_vacid_remove_inv (m,m1)
    ==>
    ntp4vc_vacid_remove_inv (m,m1) /\
    (!m2:ntp4vc_vacid_remove_tree.
       ntp4vc_vacid_remove_post m m1 k m2
       ==>
       ntp4vc_vacid_remove_post m m1 k m2)`;;
