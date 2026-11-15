(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_red_black_trees_Vacid0_lookupqtvc: the lookup verification
  condition for an integer-keyed red-black-tree map with a default value,
  relating tree membership, key absence, and returned values. This file
  contains no proof.
*)

let ntp4vc_vacid_lookup_color_INDUCT,
    ntp4vc_vacid_lookup_color_RECURSION =
  define_type
   "ntp4vc_vacid_lookup_color =
      NTP4VCVacidLookupRed
    | NTP4VCVacidLookupBlack";;

let ntp4vc_vacid_lookup_tree_INDUCT,
    ntp4vc_vacid_lookup_tree_RECURSION =
  define_type
   "ntp4vc_vacid_lookup_tree =
      NTP4VCVacidLookupLeaf
    | NTP4VCVacidLookupNode
        ntp4vc_vacid_lookup_color ntp4vc_vacid_lookup_tree int int
        ntp4vc_vacid_lookup_tree";;

let ntp4vc_vacid_lookup_memt =
  new_recursive_definition ntp4vc_vacid_lookup_tree_RECURSION
   `(!k v:int.
       ntp4vc_vacid_lookup_memt NTP4VCVacidLookupLeaf k v <=> F) /\
    (!c:ntp4vc_vacid_lookup_color.
     !l r:ntp4vc_vacid_lookup_tree.
     !k0 v0 k v:int.
       ntp4vc_vacid_lookup_memt
         (NTP4VCVacidLookupNode c l k0 v0 r) k v <=>
       (k = k0 /\ v = v0) \/
       ntp4vc_vacid_lookup_memt l k v \/
       ntp4vc_vacid_lookup_memt r k v)`;;

let ntp4vc_vacid_lookup_lt_tree = new_definition
 `ntp4vc_vacid_lookup_lt_tree
    (x:int) (t:ntp4vc_vacid_lookup_tree) <=>
    !k v:int. ntp4vc_vacid_lookup_memt t k v ==> k < x`;;

let ntp4vc_vacid_lookup_gt_tree = new_definition
 `ntp4vc_vacid_lookup_gt_tree
    (x:int) (t:ntp4vc_vacid_lookup_tree) <=>
    !k v:int. ntp4vc_vacid_lookup_memt t k v ==> x < k`;;

let ntp4vc_vacid_lookup_bst =
  new_recursive_definition ntp4vc_vacid_lookup_tree_RECURSION
   `(ntp4vc_vacid_lookup_bst NTP4VCVacidLookupLeaf <=> T) /\
    (!c:ntp4vc_vacid_lookup_color.
     !l r:ntp4vc_vacid_lookup_tree.
     !k v:int.
       ntp4vc_vacid_lookup_bst
         (NTP4VCVacidLookupNode c l k v r) <=>
       ntp4vc_vacid_lookup_bst l /\
       ntp4vc_vacid_lookup_bst r /\
       ntp4vc_vacid_lookup_lt_tree k l /\
       ntp4vc_vacid_lookup_gt_tree k r)`;;

let ntp4vc_vacid_lookup_is_not_red =
  new_recursive_definition ntp4vc_vacid_lookup_tree_RECURSION
   `(ntp4vc_vacid_lookup_is_not_red NTP4VCVacidLookupLeaf <=> T) /\
    (!c:ntp4vc_vacid_lookup_color.
     !l r:ntp4vc_vacid_lookup_tree.
     !k v:int.
       ntp4vc_vacid_lookup_is_not_red
         (NTP4VCVacidLookupNode c l k v r) <=>
       ~(c = NTP4VCVacidLookupRed))`;;

let ntp4vc_vacid_lookup_rbtree =
  new_recursive_definition ntp4vc_vacid_lookup_tree_RECURSION
   `(!n:int.
       ntp4vc_vacid_lookup_rbtree n NTP4VCVacidLookupLeaf <=>
       n = (&0:int)) /\
    (!n:int.
     !c:ntp4vc_vacid_lookup_color.
     !l r:ntp4vc_vacid_lookup_tree.
     !k v:int.
       ntp4vc_vacid_lookup_rbtree n
         (NTP4VCVacidLookupNode c l k v r) <=>
       if c = NTP4VCVacidLookupRed then
         ntp4vc_vacid_lookup_rbtree n l /\
         ntp4vc_vacid_lookup_rbtree n r /\
         ntp4vc_vacid_lookup_is_not_red l /\
         ntp4vc_vacid_lookup_is_not_red r
       else
         ntp4vc_vacid_lookup_rbtree (n - (&1:int)) l /\
         ntp4vc_vacid_lookup_rbtree (n - (&1:int)) r)`;;

let ntp4vc_vacid_lookup_inv = new_definition
 `ntp4vc_vacid_lookup_inv
    (state:int#ntp4vc_vacid_lookup_tree) <=>
    ntp4vc_vacid_lookup_bst (SND state) /\
    (?n:int. ntp4vc_vacid_lookup_rbtree n (SND state))`;;

let ntp4vc_vacid_lookup_default = new_definition
 `ntp4vc_vacid_lookup_default
    (state:int#ntp4vc_vacid_lookup_tree) =
    FST state`;;

let ntp4vc_vacid_lookup_mem = new_definition
 `ntp4vc_vacid_lookup_mem
    (state:int#ntp4vc_vacid_lookup_tree) (k:int) (v:int) <=>
    ntp4vc_vacid_lookup_memt (SND state) k v \/
    (v = ntp4vc_vacid_lookup_default state /\
     (!v':int.
        ~ntp4vc_vacid_lookup_memt (SND state) k v'))`;;

let statement =
 `!m:int.
  !m1:ntp4vc_vacid_lookup_tree.
  !k:int.
    ntp4vc_vacid_lookup_inv (m,m1)
    ==>
    ntp4vc_vacid_lookup_bst m1 /\
    (!result:int.
       (ntp4vc_vacid_lookup_memt m1 k result \/
        ((!v:int. ~ntp4vc_vacid_lookup_memt m1 k v) /\
         result = m))
       ==>
       ntp4vc_vacid_lookup_mem (m,m1) k result)`;;
