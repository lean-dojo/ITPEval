(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2016_tree_traversal_Recursive_markTreeqtvc: the recursive
  Morris binary-tree marking verification condition, including pointer
  rotations, recursive subtree traversal, marking, and restoration of the
  original tree shape. This file contains no proof.
*)

let ntp4vc_ttm_kind_INDUCT,ntp4vc_ttm_kind_RECURSION =
  define_type
   "ntp4vc_ttm_kind =
      NTP4VC_TTM_Parent
    | NTP4VC_TTM_Left
    | NTP4VC_TTM_Right";;

let ntp4vc_ttm_tree_INDUCT,ntp4vc_ttm_tree_RECURSION =
  define_type
   "ntp4vc_ttm_tree =
      NTP4VC_TTM_Empty
    | NTP4VC_TTM_Node ntp4vc_ttm_tree A ntp4vc_ttm_tree";;

let ntp4vc_ttm_phase_INDUCT,ntp4vc_ttm_phase_RECURSION =
  define_type
   "ntp4vc_ttm_phase =
      NTP4VC_TTM_GoLeft
    | NTP4VC_TTM_GoRight
    | NTP4VC_TTM_GoBack
    | NTP4VC_TTM_Finish";;

let ntp4vc_ttm_memory_INDUCT,ntp4vc_ttm_memory_RECURSION =
  define_type
   "ntp4vc_ttm_memory =
      NTP4VC_TTM_Memory
        (ntp4vc_ttm_kind->A->A)
        (A->bool)";;

let ntp4vc_ttm_accessor =
  new_recursive_definition ntp4vc_ttm_memory_RECURSION
   `!p:ntp4vc_ttm_kind->A->A.
    !m:A->bool.
      ntp4vc_ttm_accessor (NTP4VC_TTM_Memory p m) = p`;;

let ntp4vc_ttm_mark =
  new_recursive_definition ntp4vc_ttm_memory_RECURSION
   `!p:ntp4vc_ttm_kind->A->A.
    !m:A->bool.
      ntp4vc_ttm_mark (NTP4VC_TTM_Memory p m) = m`;;

let ntp4vc_ttm_update = new_definition
 `ntp4vc_ttm_update (f:A->B) (x:A) (y:B) =
    \z:A. if z = x then y else f z`;;

let ntp4vc_ttm_is_tree =
  new_recursive_definition ntp4vc_ttm_tree_RECURSION
   `(!null:A.
     !memo:ntp4vc_ttm_kind->A->A.
     !c p:A.
       ntp4vc_ttm_is_tree null memo
         (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree) c p <=>
       c = null) /\
    (!null:A.
     !memo:ntp4vc_ttm_kind->A->A.
     !l r:A ntp4vc_ttm_tree.
     !m c p:A.
       ntp4vc_ttm_is_tree null memo (NTP4VC_TTM_Node l m r) c p <=>
       ~(c = null) /\
       c = m /\
       memo NTP4VC_TTM_Parent c = p /\
       (let cl = memo NTP4VC_TTM_Left c in
        let cr = memo NTP4VC_TTM_Right c in
        (cl = null <=> cr = null) /\
        ntp4vc_ttm_is_tree null memo l cl c /\
        ntp4vc_ttm_is_tree null memo r cr c))`;;

let ntp4vc_ttm_footprint =
  new_recursive_definition ntp4vc_ttm_tree_RECURSION
   `(ntp4vc_ttm_footprint
       (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree) =
       (\x:A. F)) /\
    (!l r:A ntp4vc_ttm_tree.
     !m:A.
       ntp4vc_ttm_footprint (NTP4VC_TTM_Node l m r) =
       (\x:A.
          x = m \/
          ntp4vc_ttm_footprint l x \/
          ntp4vc_ttm_footprint r x))`;;

let ntp4vc_ttm_ext = new_definition
 `ntp4vc_ttm_ext
    (s:A->bool)
    (memo1:ntp4vc_ttm_kind->A->A)
    (memo2:ntp4vc_ttm_kind->A->A) <=>
    !k:ntp4vc_ttm_kind.
    !x:A.
      s x ==> memo1 k x = memo2 k x`;;

let ntp4vc_ttm_unchanged = new_definition
 `ntp4vc_ttm_unchanged
    (memo1:ntp4vc_ttm_kind->A->A)
    (memo2:ntp4vc_ttm_kind->A->A) <=>
    !k:ntp4vc_ttm_kind.
    !x:A.
      memo1 k x = memo2 k x`;;

let ntp4vc_ttm_was_marked = new_definition
 `ntp4vc_ttm_was_marked
    (t:A ntp4vc_ttm_tree)
    (memo1:A->bool)
    (memo2:A->bool) <=>
    (!l:A. ntp4vc_ttm_footprint t l ==> memo2 l = T) /\
    (!l:A.
       ~(ntp4vc_ttm_footprint t l) ==> memo2 l = memo1 l)`;;

let ntp4vc_ttm_next_phase =
  new_recursive_definition ntp4vc_ttm_phase_RECURSION
   `(ntp4vc_ttm_next_phase NTP4VC_TTM_GoLeft =
       NTP4VC_TTM_GoRight) /\
    (ntp4vc_ttm_next_phase NTP4VC_TTM_GoRight =
       NTP4VC_TTM_GoBack) /\
    (ntp4vc_ttm_next_phase NTP4VC_TTM_GoBack =
       NTP4VC_TTM_GoLeft) /\
    (ntp4vc_ttm_next_phase NTP4VC_TTM_Finish =
       NTP4VC_TTM_Finish)`;;

let ntp4vc_ttm_rotated = new_definition
 `ntp4vc_ttm_rotated
    (null:A)
    (memo1:ntp4vc_ttm_kind->A->A)
    (memo2:ntp4vc_ttm_kind->A->A)
    (ph:ntp4vc_ttm_phase)
    (c:A) <=>
    (!k:ntp4vc_ttm_kind.
     !x:A.
       ~(x = c) ==> memo1 k x = memo2 k x) /\
    (~(ph = NTP4VC_TTM_Finish) ==> ~(c = null)) /\
    (if ph = NTP4VC_TTM_GoLeft then
       ntp4vc_ttm_unchanged memo1 memo2
     else if ph = NTP4VC_TTM_GoRight then
       memo2 NTP4VC_TTM_Left c = memo1 NTP4VC_TTM_Right c /\
       memo2 NTP4VC_TTM_Right c = memo1 NTP4VC_TTM_Parent c /\
       memo2 NTP4VC_TTM_Parent c = memo1 NTP4VC_TTM_Left c
     else if ph = NTP4VC_TTM_GoBack then
       memo1 NTP4VC_TTM_Left c = memo2 NTP4VC_TTM_Right c /\
       memo1 NTP4VC_TTM_Right c = memo2 NTP4VC_TTM_Parent c /\
       memo1 NTP4VC_TTM_Parent c = memo2 NTP4VC_TTM_Left c
     else
       c = null)`;;

let ntp4vc_ttm_nonempty =
  new_recursive_definition ntp4vc_ttm_tree_RECURSION
   `(ntp4vc_ttm_nonempty
       (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree) = F) /\
    (!l r:A ntp4vc_ttm_tree.
     !m:A.
       ntp4vc_ttm_nonempty (NTP4VC_TTM_Node l m r) = T)`;;

let ntp4vc_ttm_has_children =
  new_recursive_definition ntp4vc_ttm_tree_RECURSION
   `(!lf rg:A ntp4vc_ttm_tree.
       ntp4vc_ttm_has_children
         (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree) lf rg <=>
       F) /\
    (!l r lf rg:A ntp4vc_ttm_tree.
     !m:A.
       ntp4vc_ttm_has_children (NTP4VC_TTM_Node l m r) lf rg <=>
       lf = l /\ rg = r)`;;

let ntp4vc_ttm_is_immediate_subtree =
  new_recursive_definition ntp4vc_ttm_tree_RECURSION
   `(!u:A ntp4vc_ttm_tree.
       ntp4vc_ttm_is_immediate_subtree
         (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree) u <=>
       F) /\
    (!l r u:A ntp4vc_ttm_tree.
     !m:A.
       ntp4vc_ttm_is_immediate_subtree
         (NTP4VC_TTM_Node l m r) u <=>
       l = u \/ r = u)`;;

let ntp4vc_ttm_leaf_bloc_result = new_definition
 `ntp4vc_ttm_leaf_bloc_result
    (null:A)
    (mem0:ntp4vc_ttm_kind->A->A)
    (memo1:A ntp4vc_ttm_memory)
    (ph:ntp4vc_ttm_phase)
    (x:A)
    (memo2:A ntp4vc_ttm_memory) <=>
    ~(x = null) /\
    ~(ph = NTP4VC_TTM_Finish) /\
    ntp4vc_ttm_mark memo2 x = T /\
    (!l:A.
       ~(l = x) ==> ntp4vc_ttm_mark memo2 l = ntp4vc_ttm_mark memo1 l) /\
    (if
       ntp4vc_ttm_accessor memo1 NTP4VC_TTM_Left x = null /\
       null = ntp4vc_ttm_accessor memo1 NTP4VC_TTM_Right x
     then
       ntp4vc_ttm_accessor memo2 = ntp4vc_ttm_accessor memo1
     else
       ntp4vc_ttm_rotated null mem0 (ntp4vc_ttm_accessor memo2)
         (ntp4vc_ttm_next_phase ph) x)`;;

let ntp4vc_ttm_rotated_bloc_result = new_definition
 `ntp4vc_ttm_rotated_bloc_result
    (null:A)
    (mem0:ntp4vc_ttm_kind->A->A)
    (memo1:A ntp4vc_ttm_memory)
    (ph:ntp4vc_ttm_phase)
    (x:A)
    (memo2:A ntp4vc_ttm_memory) <=>
    ~(x = null) /\
    ~(x = null) /\
    (let o5 = NTP4VC_TTM_Left in
     ~(x = null) /\
     (!memo3:A ntp4vc_ttm_memory.
        ntp4vc_ttm_mark memo3 = ntp4vc_ttm_mark memo2
        ==>
        ntp4vc_ttm_accessor memo3 =
          ntp4vc_ttm_update (ntp4vc_ttm_accessor memo2) o5
            (ntp4vc_ttm_update (ntp4vc_ttm_accessor memo2 o5) x
              (ntp4vc_ttm_accessor memo2 NTP4VC_TTM_Right x))
        ==>
        ~(x = null) /\
        (let o6 = NTP4VC_TTM_Right in
         ~(x = null) /\
         (!memo4:A ntp4vc_ttm_memory.
            ntp4vc_ttm_mark memo4 = ntp4vc_ttm_mark memo3
            ==>
            ntp4vc_ttm_accessor memo4 =
              ntp4vc_ttm_update (ntp4vc_ttm_accessor memo3) o6
                (ntp4vc_ttm_update (ntp4vc_ttm_accessor memo3 o6) x
                  (ntp4vc_ttm_accessor memo3 NTP4VC_TTM_Parent x))
            ==>
            (let o7 = NTP4VC_TTM_Parent in
             ~(x = null) /\
             (!memo5:A ntp4vc_ttm_memory.
                ntp4vc_ttm_mark memo5 = ntp4vc_ttm_mark memo4
                ==>
                ntp4vc_ttm_accessor memo5 =
                  ntp4vc_ttm_update (ntp4vc_ttm_accessor memo4) o7
                    (ntp4vc_ttm_update
                      (ntp4vc_ttm_accessor memo4 o7) x
                      (ntp4vc_ttm_accessor memo2 NTP4VC_TTM_Left x))
                ==>
                ntp4vc_ttm_accessor memo2 NTP4VC_TTM_Left x =
                  ntp4vc_ttm_accessor memo5 NTP4VC_TTM_Parent x /\
                ~(ph = NTP4VC_TTM_Finish) /\
                ntp4vc_ttm_mark memo5 x = T /\
                (!l:A.
                   ~(l = x)
                   ==>
                   ntp4vc_ttm_mark memo5 l =
                     ntp4vc_ttm_mark memo1 l) /\
                (if
                   ntp4vc_ttm_accessor memo1 NTP4VC_TTM_Left x = null /\
                   null =
                     ntp4vc_ttm_accessor memo1 NTP4VC_TTM_Right x
                 then
                   ntp4vc_ttm_accessor memo5 =
                     ntp4vc_ttm_accessor memo1
                 else
                   ntp4vc_ttm_rotated null mem0
                     (ntp4vc_ttm_accessor memo5)
                     (ntp4vc_ttm_next_phase ph) x)))))))`;;

let ntp4vc_ttm_after_mark_bloc_vc = new_definition
 `ntp4vc_ttm_after_mark_bloc_vc
    (null:A)
    (mem0:ntp4vc_ttm_kind->A->A)
    (memo1:A ntp4vc_ttm_memory)
    (ph:ntp4vc_ttm_phase)
    (x:A)
    (memo2:A ntp4vc_ttm_memory) <=>
    ~(x = null) /\
    (let o3 = ntp4vc_ttm_accessor memo2 NTP4VC_TTM_Left x in
     (o3 = null ==> ~(x = null)) /\
     (!o4:bool.
        (if o3 = null then
           o4 =
             (if ntp4vc_ttm_accessor memo2 NTP4VC_TTM_Right x = null
              then T else F)
         else
           o4 = F)
        ==>
        if o4 = T then
          ntp4vc_ttm_leaf_bloc_result null mem0 memo1 ph x memo2
        else
          ntp4vc_ttm_rotated_bloc_result null mem0 memo1 ph x memo2))`;;

let ntp4vc_ttm_bloc_vc = new_definition
 `ntp4vc_ttm_bloc_vc
    (null:A)
    (entered:bool)
    (x:A)
    (memo1:A ntp4vc_ttm_memory)
    (mem0:ntp4vc_ttm_kind->A->A)
    (ph:ntp4vc_ttm_phase) <=>
    ntp4vc_ttm_rotated null mem0 (ntp4vc_ttm_accessor memo1) ph x /\
    (ph = NTP4VC_TTM_Finish ==> entered = T)
    ==>
    !o2:bool.
      (if entered = T then
         o2 = (if x = null then T else F)
       else
         o2 = F)
      ==>
      if o2 = T then
        ph = NTP4VC_TTM_Finish
      else
        ~(x = null) /\
        (!memo2:A ntp4vc_ttm_memory.
           ntp4vc_ttm_accessor memo2 = ntp4vc_ttm_accessor memo1
           ==>
           ntp4vc_ttm_mark memo2 =
             ntp4vc_ttm_update (ntp4vc_ttm_mark memo1) x T
           ==>
           ntp4vc_ttm_after_mark_bloc_vc
             null mem0 memo1 ph x memo2)`;;

let ntp4vc_ttm_result_vc = new_definition
 `ntp4vc_ttm_result_vc
    (null:A)
    (x_lf:A)
    (x_rg:A)
    (lf:A ntp4vc_ttm_tree)
    (rg:A ntp4vc_ttm_tree)
    (result:bool) <=>
    (if x_lf = null then
       result = (if x_rg = null then T else F)
     else
       result = F)
    ==>
    (result = T <=> x_lf = null /\ x_rg = null) /\
    (result = T
     ==>
     lf = (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree) /\
     rg = (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree))`;;

let ntp4vc_ttm_after_go_back = new_definition
 `ntp4vc_ttm_after_go_back
    (null:A)
    (t1:A ntp4vc_ttm_tree)
    (z:A)
    (x:A)
    (memo1:A ntp4vc_ttm_memory)
    (mem0:ntp4vc_ttm_kind->A->A)
    (memo5:A ntp4vc_ttm_memory) <=>
    (let o4 = NTP4VC_TTM_GoBack in
     ntp4vc_ttm_rotated null mem0 (ntp4vc_ttm_accessor memo5) o4 x /\
     (!memo6:A ntp4vc_ttm_memory.
        ntp4vc_ttm_mark memo6 x = T /\
        (!l:A.
           ~(l = x)
           ==>
           ntp4vc_ttm_mark memo6 l = ntp4vc_ttm_mark memo5 l) /\
        (if
           ntp4vc_ttm_accessor memo5 NTP4VC_TTM_Left x = null /\
           null = ntp4vc_ttm_accessor memo5 NTP4VC_TTM_Right x
         then
           ntp4vc_ttm_accessor memo6 = ntp4vc_ttm_accessor memo5
         else
           ntp4vc_ttm_rotated null mem0 (ntp4vc_ttm_accessor memo6)
             (ntp4vc_ttm_next_phase o4) x)
        ==>
        ntp4vc_ttm_unchanged
          (ntp4vc_ttm_accessor memo1) (ntp4vc_ttm_accessor memo6) /\
        ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Parent x = z /\
        ntp4vc_ttm_was_marked t1
          (ntp4vc_ttm_mark memo1) (ntp4vc_ttm_mark memo6)))`;;

let ntp4vc_ttm_after_right_traversal = new_definition
 `ntp4vc_ttm_after_right_traversal
    (null:A)
    (t1:A ntp4vc_ttm_tree)
    (rg:A ntp4vc_ttm_tree)
    (x_lf:A)
    (x_rg:A)
    (z:A)
    (x:A)
    (memo1:A ntp4vc_ttm_memory)
    (mem0:ntp4vc_ttm_kind->A->A)
    (memo4:A ntp4vc_ttm_memory) <=>
    (ntp4vc_ttm_ext (ntp4vc_ttm_footprint rg) mem0
       (ntp4vc_ttm_accessor memo4) /\
     ntp4vc_ttm_is_tree null mem0 rg x_rg x) /\
    (ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo4) rg x_rg x
     ==>
     (ntp4vc_ttm_is_immediate_subtree t1 rg /\
      ~(ntp4vc_ttm_accessor memo4 NTP4VC_TTM_Parent x = null) /\
      ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo4) rg
        (ntp4vc_ttm_accessor memo4 NTP4VC_TTM_Parent x) x) /\
     (!memo5:A ntp4vc_ttm_memory.
        ntp4vc_ttm_unchanged
          (ntp4vc_ttm_accessor memo4) (ntp4vc_ttm_accessor memo5) /\
        ntp4vc_ttm_was_marked rg
          (ntp4vc_ttm_mark memo4) (ntp4vc_ttm_mark memo5)
        ==>
        ntp4vc_ttm_after_go_back
          null t1 z x memo1 mem0 memo5))`;;

let ntp4vc_ttm_after_left_traversal = new_definition
 `ntp4vc_ttm_after_left_traversal
    (null:A)
    (t1:A ntp4vc_ttm_tree)
    (lf:A ntp4vc_ttm_tree)
    (rg:A ntp4vc_ttm_tree)
    (x_lf:A)
    (x_rg:A)
    (z:A)
    (x:A)
    (memo1:A ntp4vc_ttm_memory)
    (mem0:ntp4vc_ttm_kind->A->A)
    (memo2:A ntp4vc_ttm_memory) <=>
    (ntp4vc_ttm_ext (ntp4vc_ttm_footprint lf) mem0
       (ntp4vc_ttm_accessor memo2) /\
     ntp4vc_ttm_is_tree null mem0 lf x_lf x) /\
    (ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo2) lf x_lf x
     ==>
     (ntp4vc_ttm_is_immediate_subtree t1 lf /\
      ~(ntp4vc_ttm_accessor memo2 NTP4VC_TTM_Parent x = null) /\
      ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo2) lf
        (ntp4vc_ttm_accessor memo2 NTP4VC_TTM_Parent x) x) /\
     (!memo3:A ntp4vc_ttm_memory.
        ntp4vc_ttm_unchanged
          (ntp4vc_ttm_accessor memo2) (ntp4vc_ttm_accessor memo3) /\
        ntp4vc_ttm_was_marked lf
          (ntp4vc_ttm_mark memo2) (ntp4vc_ttm_mark memo3)
        ==>
        (let o3 = NTP4VC_TTM_GoRight in
         ntp4vc_ttm_rotated null mem0
           (ntp4vc_ttm_accessor memo3) o3 x /\
         (!memo4:A ntp4vc_ttm_memory.
            ntp4vc_ttm_mark memo4 x = T /\
            (!l:A.
               ~(l = x)
               ==>
               ntp4vc_ttm_mark memo4 l =
                 ntp4vc_ttm_mark memo3 l) /\
            (if
               ntp4vc_ttm_accessor memo3 NTP4VC_TTM_Left x = null /\
               null = ntp4vc_ttm_accessor memo3 NTP4VC_TTM_Right x
             then
               ntp4vc_ttm_accessor memo4 =
                 ntp4vc_ttm_accessor memo3
             else
               ntp4vc_ttm_rotated null mem0
                 (ntp4vc_ttm_accessor memo4)
                 (ntp4vc_ttm_next_phase o3) x)
            ==>
            ntp4vc_ttm_after_right_traversal
              null t1 rg x_lf x_rg z x memo1 mem0 memo4))))`;;

let ntp4vc_ttm_subtree_branch_vc = new_definition
 `ntp4vc_ttm_subtree_branch_vc
    (null:A)
    (t1:A ntp4vc_ttm_tree)
    (lf:A ntp4vc_ttm_tree)
    (rg:A ntp4vc_ttm_tree)
    (x_lf:A)
    (x_rg:A)
    (z:A)
    (x:A)
    (memo1:A ntp4vc_ttm_memory)
    (mem0:ntp4vc_ttm_kind->A->A)
    (memo2:A ntp4vc_ttm_memory) <=>
    (!result:bool.
       ntp4vc_ttm_result_vc null x_lf x_rg lf rg result) /\
    ((x_lf = null /\ x_rg = null
      ==>
      lf = (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree) /\
      rg = (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree))
     ==>
     if ~(x_lf = null /\ x_rg = null) then
       ntp4vc_ttm_after_left_traversal
         null t1 lf rg x_lf x_rg z x memo1 mem0 memo2
     else
       ntp4vc_ttm_unchanged
         (ntp4vc_ttm_accessor memo1) (ntp4vc_ttm_accessor memo2) /\
       ntp4vc_ttm_accessor memo2 NTP4VC_TTM_Parent x = z /\
       ntp4vc_ttm_was_marked t1
         (ntp4vc_ttm_mark memo1) (ntp4vc_ttm_mark memo2))`;;

let ntp4vc_ttm_after_first_bloc = new_definition
 `ntp4vc_ttm_after_first_bloc
    (null:A)
    (t1:A ntp4vc_ttm_tree)
    (lf:A ntp4vc_ttm_tree)
    (rg:A ntp4vc_ttm_tree)
    (x_lf:A)
    (x_rg:A)
    (z:A)
    (x:A)
    (memo1:A ntp4vc_ttm_memory)
    (mem0:ntp4vc_ttm_kind->A->A)
    (memo2:A ntp4vc_ttm_memory) <=>
    ntp4vc_ttm_mark memo2 x = T /\
    (!l:A.
       ~(l = x) ==> ntp4vc_ttm_mark memo2 l = ntp4vc_ttm_mark memo1 l) /\
    (if
       ntp4vc_ttm_accessor memo1 NTP4VC_TTM_Left x = null /\
       null = ntp4vc_ttm_accessor memo1 NTP4VC_TTM_Right x
     then
       ntp4vc_ttm_accessor memo2 = ntp4vc_ttm_accessor memo1
     else
       ntp4vc_ttm_rotated null mem0 (ntp4vc_ttm_accessor memo2)
         (ntp4vc_ttm_next_phase NTP4VC_TTM_GoLeft) x)
    ==>
    ntp4vc_ttm_subtree_branch_vc
      null t1 lf rg x_lf x_rg z x memo1 mem0 memo2`;;

let ntp4vc_ttm_recursive_case_vc = new_definition
 `ntp4vc_ttm_recursive_case_vc
    (null:A)
    (z:A)
    (x:A)
    (memo1:A ntp4vc_ttm_memory)
    (t1:A ntp4vc_ttm_tree) <=>
    ~(x = null) /\
    ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo1) t1 x z
    ==>
    (let mem0 = ntp4vc_ttm_accessor memo1 in
     ~(x = null) /\
     (let x_lf = ntp4vc_ttm_accessor memo1 NTP4VC_TTM_Left x in
      ~(x = null) /\
      (let x_rg = ntp4vc_ttm_accessor memo1 NTP4VC_TTM_Right x in
       ntp4vc_ttm_nonempty t1 /\
       (!lf rg:A ntp4vc_ttm_tree.
          ntp4vc_ttm_has_children t1 lf rg
          ==>
          ntp4vc_ttm_is_tree null mem0
            (NTP4VC_TTM_Node lf x rg) x z /\
          (~(ntp4vc_ttm_footprint lf x) /\
           ~(ntp4vc_ttm_footprint rg x)
           ==>
           ntp4vc_ttm_rotated null mem0
             (ntp4vc_ttm_accessor memo1) NTP4VC_TTM_GoLeft x /\
           (!memo2:A ntp4vc_ttm_memory.
              ntp4vc_ttm_after_first_bloc
                null t1 lf rg x_lf x_rg z x memo1 mem0 memo2))))))`;;

let ntp4vc_ttm_final_vc = new_definition
 `ntp4vc_ttm_final_vc
    (null:A)
    (memo:A ntp4vc_ttm_memory)
    (t:A ntp4vc_ttm_tree)
    (root:A) <=>
    (let o1 = null in
     let mem0 = ntp4vc_ttm_accessor memo in
     (~(root = null) /\
      ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo) t root o1) /\
     (!memo1:A ntp4vc_ttm_memory.
        ntp4vc_ttm_unchanged
          (ntp4vc_ttm_accessor memo) (ntp4vc_ttm_accessor memo1) /\
        ntp4vc_ttm_was_marked t
          (ntp4vc_ttm_mark memo) (ntp4vc_ttm_mark memo1)
        ==>
        ntp4vc_ttm_rotated null mem0
          (ntp4vc_ttm_accessor memo1) NTP4VC_TTM_Finish o1 /\
        (!x:A.
           ntp4vc_ttm_rotated null mem0
             (ntp4vc_ttm_accessor memo1) NTP4VC_TTM_Finish x
           ==>
           ntp4vc_ttm_rotated null mem0
             (ntp4vc_ttm_accessor memo1) NTP4VC_TTM_Finish x /\
           (let o2 = null in
            (ntp4vc_ttm_ext (ntp4vc_ttm_footprint t) mem0
               (ntp4vc_ttm_accessor memo1) /\
             ntp4vc_ttm_is_tree null mem0 t root o2) /\
            (ntp4vc_ttm_is_tree null
               (ntp4vc_ttm_accessor memo1) t root o2
             ==>
             ntp4vc_ttm_is_tree null
               (ntp4vc_ttm_accessor memo1) t root null /\
             ntp4vc_ttm_unchanged
               (ntp4vc_ttm_accessor memo)
               (ntp4vc_ttm_accessor memo1) /\
             ntp4vc_ttm_was_marked t
               (ntp4vc_ttm_mark memo)
               (ntp4vc_ttm_mark memo1))))))`;;

let statement =
 `!null:A.
  !memo:A ntp4vc_ttm_memory.
  !t:A ntp4vc_ttm_tree.
  !root:A.
    ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo) t root null
    ==>
    ~(root = null)
    ==>
    (let o1 = null in
     ((!entered:bool.
       !x:A.
       !memo1:A ntp4vc_ttm_memory.
       !mem0:ntp4vc_ttm_kind->A->A.
       !ph:ntp4vc_ttm_phase.
         ntp4vc_ttm_bloc_vc null entered x memo1 mem0 ph) /\
      (!z x:A.
       !memo1:A ntp4vc_ttm_memory.
       !t1:A ntp4vc_ttm_tree.
         ntp4vc_ttm_recursive_case_vc null z x memo1 t1)) /\
     ntp4vc_ttm_final_vc null memo t root)`;;
