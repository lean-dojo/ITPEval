(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2016_tree_traversal_Iterative_markTreeqtvc: the generated
  verification condition for iterative constant-space binary-tree marking,
  including tree shape, simulated call-stack, pointer-rotation, marking, and
  termination invariants. This file contains no proof.
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

let ntp4vc_ttm_snap_INDUCT,ntp4vc_ttm_snap_RECURSION =
  define_type
   "ntp4vc_ttm_snap =
      NTP4VC_TTM_Snap
        (ntp4vc_ttm_kind->A->A)
        A A (A->bool)";;

let ntp4vc_ttm_frame_INDUCT,ntp4vc_ttm_frame_RECURSION =
  define_type
   "ntp4vc_ttm_frame =
      NTP4VC_TTM_Frame
        (A ntp4vc_ttm_snap)
        (A ntp4vc_ttm_tree)
        (A ntp4vc_ttm_tree)
        A
        (A ntp4vc_ttm_tree)
        A
        (A ntp4vc_ttm_snap)
        (A ntp4vc_ttm_snap)
        (A ntp4vc_ttm_snap)
        (A ntp4vc_ttm_snap)";;

let ntp4vc_ttm_stack_INDUCT,ntp4vc_ttm_stack_RECURSION =
  define_type
   "ntp4vc_ttm_stack =
      NTP4VC_TTM_Bottom
    | NTP4VC_TTM_Running
        ntp4vc_ttm_stack int (A ntp4vc_ttm_frame)
    | NTP4VC_TTM_Done";;

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

let ntp4vc_ttm_pointers =
  new_recursive_definition ntp4vc_ttm_snap_RECURSION
   `!p:ntp4vc_ttm_kind->A->A.
    !c q:A.
    !m:A->bool.
      ntp4vc_ttm_pointers (NTP4VC_TTM_Snap p c q m) = p`;;

let ntp4vc_ttm_cursor =
  new_recursive_definition ntp4vc_ttm_snap_RECURSION
   `!p:ntp4vc_ttm_kind->A->A.
    !c q:A.
    !m:A->bool.
      ntp4vc_ttm_cursor (NTP4VC_TTM_Snap p c q m) = c`;;

let ntp4vc_ttm_parent =
  new_recursive_definition ntp4vc_ttm_snap_RECURSION
   `!p:ntp4vc_ttm_kind->A->A.
    !c q:A.
    !m:A->bool.
      ntp4vc_ttm_parent (NTP4VC_TTM_Snap p c q m) = q`;;

let ntp4vc_ttm_marks =
  new_recursive_definition ntp4vc_ttm_snap_RECURSION
   `!p:ntp4vc_ttm_kind->A->A.
    !c q:A.
    !m:A->bool.
      ntp4vc_ttm_marks (NTP4VC_TTM_Snap p c q m) = m`;;

let ntp4vc_ttm_memo0 =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_memo0
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = m0`;;

let ntp4vc_ttm_frame_tree =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_frame_tree
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = t`;;

let ntp4vc_ttm_tleft =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_tleft
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = tl`;;

let ntp4vc_ttm_pleft =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_pleft
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = pl`;;

let ntp4vc_ttm_tright =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_tright
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = tr`;;

let ntp4vc_ttm_pright =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_pright
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = pr`;;

let ntp4vc_ttm_memo1 =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_memo1
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = m1`;;

let ntp4vc_ttm_memo2 =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_memo2
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = m2`;;

let ntp4vc_ttm_memo3 =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_memo3
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = m3`;;

let ntp4vc_ttm_memo4 =
  new_recursive_definition ntp4vc_ttm_frame_RECURSION
   `!m0:A ntp4vc_ttm_snap.
    !t tl:A ntp4vc_ttm_tree.
    !pl:A.
    !tr:A ntp4vc_ttm_tree.
    !pr:A.
    !m1 m2 m3 m4:A ntp4vc_ttm_snap.
      ntp4vc_ttm_memo4
        (NTP4VC_TTM_Frame m0 t tl pl tr pr m1 m2 m3 m4) = m4`;;

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

let ntp4vc_ttm_size =
  new_recursive_definition ntp4vc_ttm_tree_RECURSION
   `(ntp4vc_ttm_size
       (NTP4VC_TTM_Empty:A ntp4vc_ttm_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_ttm_tree.
     !m:A.
       ntp4vc_ttm_size (NTP4VC_TTM_Node l m r) =
       (&1:int) + ntp4vc_ttm_size l + ntp4vc_ttm_size r)`;;

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
    (!l:A. ntp4vc_ttm_footprint t l ==> memo2 l) /\
    (!l:A. ~(ntp4vc_ttm_footprint t l) ==> memo2 l = memo1 l)`;;

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

let ntp4vc_ttm_frame_memo = new_definition
 `ntp4vc_ttm_frame_memo (f:A ntp4vc_ttm_frame) (pc:int) =
    if pc <= (&0:int) then ntp4vc_ttm_memo0 f
    else if pc <= (&1:int) then ntp4vc_ttm_memo1 f
    else if pc <= (&2:int) then ntp4vc_ttm_memo2 f
    else if pc <= (&3:int) then ntp4vc_ttm_memo3 f
    else ntp4vc_ttm_memo4 f`;;

let ntp4vc_ttm_bloc_rel = new_definition
 `ntp4vc_ttm_bloc_rel
    (null:A)
    (mem0:ntp4vc_ttm_kind->A->A)
    (ph:ntp4vc_ttm_phase)
    (s1:A ntp4vc_ttm_snap)
    (s2:A ntp4vc_ttm_snap) <=>
    ntp4vc_ttm_parent s2 = ntp4vc_ttm_cursor s1 /\
    ntp4vc_ttm_cursor s2 =
      ntp4vc_ttm_pointers s2 NTP4VC_TTM_Parent
        (ntp4vc_ttm_parent s2) /\
    ntp4vc_ttm_marks s2 (ntp4vc_ttm_parent s2) = T /\
    (!l:A.
       ~(l = ntp4vc_ttm_parent s2)
       ==> ntp4vc_ttm_marks s2 l = ntp4vc_ttm_marks s1 l) /\
    (if
       ntp4vc_ttm_pointers s1 NTP4VC_TTM_Left
         (ntp4vc_ttm_cursor s1) = null /\
       null =
         ntp4vc_ttm_pointers s1 NTP4VC_TTM_Right
           (ntp4vc_ttm_cursor s1)
     then
       ntp4vc_ttm_pointers s2 = ntp4vc_ttm_pointers s1
     else
       ntp4vc_ttm_rotated null mem0 (ntp4vc_ttm_pointers s2)
         (ntp4vc_ttm_next_phase ph) (ntp4vc_ttm_parent s2))`;;

let ntp4vc_ttm_rec_rel = new_definition
 `ntp4vc_ttm_rec_rel
    (t:A ntp4vc_ttm_tree)
    (s1:A ntp4vc_ttm_snap)
    (s2:A ntp4vc_ttm_snap) <=>
    ntp4vc_ttm_unchanged
      (ntp4vc_ttm_pointers s1) (ntp4vc_ttm_pointers s2) /\
    ntp4vc_ttm_cursor s2 = ntp4vc_ttm_parent s1 /\
    ntp4vc_ttm_parent s2 = ntp4vc_ttm_cursor s1 /\
    ntp4vc_ttm_was_marked t
      (ntp4vc_ttm_marks s1) (ntp4vc_ttm_marks s2)`;;

let ntp4vc_ttm_call_match =
  new_recursive_definition option_RECURSION
   `(!pc:int.
     !f:A ntp4vc_ttm_frame.
       ntp4vc_ttm_call_match pc f
         (NONE:(A ntp4vc_ttm_tree)option) <=>
       ~(pc = (&1:int)) /\ ~(pc = (&3:int))) /\
    (!pc:int.
     !f:A ntp4vc_ttm_frame.
     !u:A ntp4vc_ttm_tree.
       ntp4vc_ttm_call_match pc f (SOME u) <=>
       (if pc = (&1:int)
        then u = ntp4vc_ttm_tleft f
        else pc = (&3:int) /\ u = ntp4vc_ttm_tright f))`;;

let ntp4vc_ttm_is_stack =
  new_recursive_definition ntp4vc_ttm_stack_RECURSION
   `(!null:A.
     !t:A ntp4vc_ttm_tree.
     !stop scur:A ntp4vc_ttm_snap.
     !calls:(A ntp4vc_ttm_tree)option.
       ntp4vc_ttm_is_stack null t stop scur
         (NTP4VC_TTM_Bottom:A ntp4vc_ttm_stack) calls <=>
       stop = scur /\ calls = SOME t) /\
    (!null:A.
     !t:A ntp4vc_ttm_tree.
     !stop scur:A ntp4vc_ttm_snap.
     !s:A ntp4vc_ttm_stack.
     !pc:int.
     !f:A ntp4vc_ttm_frame.
     !calls:(A ntp4vc_ttm_tree)option.
       ntp4vc_ttm_is_stack null t stop scur
         (NTP4VC_TTM_Running s pc f) calls <=>
       (&0:int) <= pc /\ pc <= (&4:int) /\
       (let m0 = ntp4vc_ttm_memo0 f in
        ntp4vc_ttm_is_stack null t stop m0 s
          (SOME (ntp4vc_ttm_frame_tree f)) /\
        ~(ntp4vc_ttm_cursor m0 = null) /\
        ntp4vc_ttm_is_tree null (ntp4vc_ttm_pointers m0)
          (ntp4vc_ttm_frame_tree f)
          (ntp4vc_ttm_cursor m0) (ntp4vc_ttm_parent m0) /\
        ntp4vc_ttm_frame_tree f =
          NTP4VC_TTM_Node
            (ntp4vc_ttm_tleft f)
            (ntp4vc_ttm_cursor m0)
            (ntp4vc_ttm_tright f) /\
        ntp4vc_ttm_pleft f =
          ntp4vc_ttm_pointers m0 NTP4VC_TTM_Left
            (ntp4vc_ttm_cursor m0) /\
        ntp4vc_ttm_pright f =
          ntp4vc_ttm_pointers m0 NTP4VC_TTM_Right
            (ntp4vc_ttm_cursor m0) /\
        ((&1:int) <= pc
         ==>
         ntp4vc_ttm_bloc_rel null (ntp4vc_ttm_pointers m0)
           NTP4VC_TTM_GoLeft m0 (ntp4vc_ttm_memo1 f) /\
         ~(ntp4vc_ttm_pleft f = null) /\
         ~(ntp4vc_ttm_pright f = null)) /\
        ((&2:int) <= pc
         ==>
         ntp4vc_ttm_rec_rel (ntp4vc_ttm_tleft f)
           (ntp4vc_ttm_memo1 f) (ntp4vc_ttm_memo2 f)) /\
        ((&3:int) <= pc
         ==>
         ntp4vc_ttm_bloc_rel null (ntp4vc_ttm_pointers m0)
           NTP4VC_TTM_GoRight
           (ntp4vc_ttm_memo2 f) (ntp4vc_ttm_memo3 f)) /\
        ((&4:int) <= pc
         ==>
         ntp4vc_ttm_rec_rel (ntp4vc_ttm_tright f)
           (ntp4vc_ttm_memo3 f) (ntp4vc_ttm_memo4 f)) /\
        ntp4vc_ttm_frame_memo f pc = scur /\
        ntp4vc_ttm_call_match pc f calls)) /\
    (!null:A.
     !t:A ntp4vc_ttm_tree.
     !stop scur:A ntp4vc_ttm_snap.
     !calls:(A ntp4vc_ttm_tree)option.
       ntp4vc_ttm_is_stack null t stop scur
         (NTP4VC_TTM_Done:A ntp4vc_ttm_stack) calls <=>
       ntp4vc_ttm_rec_rel t stop scur /\ calls = NONE)`;;

let ntp4vc_ttm_stack_size =
  new_recursive_definition ntp4vc_ttm_stack_RECURSION
   `(ntp4vc_ttm_stack_size
       (NTP4VC_TTM_Bottom:A ntp4vc_ttm_stack) =
       (&1:int)) /\
    (ntp4vc_ttm_stack_size
       (NTP4VC_TTM_Done:A ntp4vc_ttm_stack) =
       (&0:int)) /\
    (!s:A ntp4vc_ttm_stack.
     !pc:int.
     !f:A ntp4vc_ttm_frame.
       ntp4vc_ttm_stack_size (NTP4VC_TTM_Running s pc f) =
       ntp4vc_ttm_stack_size s +
       ((&100:int) - pc) +
       (if pc = (&0:int) then
          (&100:int) *
          (ntp4vc_ttm_size (ntp4vc_ttm_tleft f) +
           ntp4vc_ttm_size (ntp4vc_ttm_tright f))
        else if pc <= (&2:int) then
          (&100:int) * ntp4vc_ttm_size (ntp4vc_ttm_tright f)
        else
          (&0:int)))`;;

let ntp4vc_ttm_initial_snap = new_definition
 `ntp4vc_ttm_initial_snap
    (null:A)
    (memo:A ntp4vc_ttm_memory)
    (root:A)
    (stop:A ntp4vc_ttm_snap) <=>
    ntp4vc_ttm_pointers stop = ntp4vc_ttm_accessor memo /\
    ntp4vc_ttm_cursor stop = root /\
    ntp4vc_ttm_parent stop = null /\
    ntp4vc_ttm_marks stop = ntp4vc_ttm_mark memo`;;

let ntp4vc_ttm_snapshot = new_definition
 `ntp4vc_ttm_snapshot
    (memo:A ntp4vc_ttm_memory)
    (cursor:A)
    (parent:A)
    (s:A ntp4vc_ttm_snap) <=>
    ntp4vc_ttm_pointers s = ntp4vc_ttm_accessor memo /\
    ntp4vc_ttm_cursor s = cursor /\
    ntp4vc_ttm_parent s = parent /\
    ntp4vc_ttm_marks s = ntp4vc_ttm_mark memo`;;

let ntp4vc_ttm_phase_at = new_definition
 `ntp4vc_ttm_phase_at (pc:int) =
    if pc = (&0:int) then NTP4VC_TTM_GoLeft
    else if pc = (&2:int) then NTP4VC_TTM_GoRight
    else NTP4VC_TTM_GoBack`;;

let ntp4vc_ttm_stack_bloc =
  new_recursive_definition ntp4vc_ttm_stack_RECURSION
   `(!null:A.
     !scur next:A ntp4vc_ttm_snap.
       ntp4vc_ttm_stack_bloc null
         (NTP4VC_TTM_Bottom:A ntp4vc_ttm_stack) scur next <=>
       F) /\
    (!null:A.
     !s:A ntp4vc_ttm_stack.
     !pc:int.
     !f:A ntp4vc_ttm_frame.
     !scur next:A ntp4vc_ttm_snap.
       ntp4vc_ttm_stack_bloc null
         (NTP4VC_TTM_Running s pc f) scur next <=>
       ntp4vc_ttm_bloc_rel null
         (ntp4vc_ttm_pointers (ntp4vc_ttm_memo0 f))
         (ntp4vc_ttm_phase_at pc) scur next) /\
    (!null:A.
     !scur next:A ntp4vc_ttm_snap.
       ntp4vc_ttm_stack_bloc null
         (NTP4VC_TTM_Done:A ntp4vc_ttm_stack) scur next <=>
       F)`;;

let ntp4vc_ttm_transition_post = new_definition
 `ntp4vc_ttm_transition_post
    (null:A)
    (t:A ntp4vc_ttm_tree)
    (stop:A ntp4vc_ttm_snap)
    (scur:A ntp4vc_ttm_snap)
    (st1:A ntp4vc_ttm_stack)
    (memo:A ntp4vc_ttm_memory)
    (next:A ntp4vc_ttm_snap)
    (target:A)
    (guard:bool) <=>
    (ntp4vc_ttm_is_stack null t stop scur st1 NONE /\
     ntp4vc_ttm_stack_bloc null st1 scur next) /\
    (!st2:A ntp4vc_ttm_stack.
       ntp4vc_ttm_is_stack null t stop next st2 NONE /\
       ntp4vc_ttm_stack_size st2 < ntp4vc_ttm_stack_size st1
       ==>
       ((&0:int) <= ntp4vc_ttm_stack_size st1 /\
        ntp4vc_ttm_stack_size st2 < ntp4vc_ttm_stack_size st1) /\
       (guard ==> T) /\
       ntp4vc_ttm_snapshot memo target
         (ntp4vc_ttm_cursor scur) next /\
       ntp4vc_ttm_is_stack null t stop next st2 NONE)`;;

let ntp4vc_ttm_leaf_or_rotate = new_definition
 `ntp4vc_ttm_leaf_or_rotate
    (null:A)
    (t:A ntp4vc_ttm_tree)
    (stop:A ntp4vc_ttm_snap)
    (st1:A ntp4vc_ttm_stack)
    (scur:A ntp4vc_ttm_snap)
    (memo6:A ntp4vc_ttm_memory)
    (o3:bool) <=>
    if o3 = T then
      ~(ntp4vc_ttm_cursor scur = null) /\
      (!o4:A ntp4vc_ttm_snap.
         ntp4vc_ttm_snapshot memo6
           (ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Parent
             (ntp4vc_ttm_cursor scur))
           (ntp4vc_ttm_cursor scur) o4
         ==>
         ntp4vc_ttm_transition_post null t stop scur st1 memo6 o4
           (ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Parent
             (ntp4vc_ttm_cursor scur))
           (ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Parent
             (ntp4vc_ttm_cursor scur) = null))
    else
      ~(ntp4vc_ttm_cursor scur = null) /\
      ~(ntp4vc_ttm_cursor scur = null) /\
      (let o4 = NTP4VC_TTM_Left in
       ~(ntp4vc_ttm_cursor scur = null) /\
       (!memo7:A ntp4vc_ttm_memory.
          ntp4vc_ttm_mark memo7 = ntp4vc_ttm_mark memo6
          ==>
          ntp4vc_ttm_accessor memo7 =
            ntp4vc_ttm_update (ntp4vc_ttm_accessor memo6) o4
              (ntp4vc_ttm_update
                (ntp4vc_ttm_accessor memo6 o4)
                (ntp4vc_ttm_cursor scur)
                (ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Right
                  (ntp4vc_ttm_cursor scur)))
          ==>
          ~(ntp4vc_ttm_cursor scur = null) /\
          (let o5 = NTP4VC_TTM_Right in
           ~(ntp4vc_ttm_cursor scur = null) /\
           (!memo8:A ntp4vc_ttm_memory.
              ntp4vc_ttm_mark memo8 = ntp4vc_ttm_mark memo7
              ==>
              ntp4vc_ttm_accessor memo8 =
                ntp4vc_ttm_update (ntp4vc_ttm_accessor memo7) o5
                  (ntp4vc_ttm_update
                    (ntp4vc_ttm_accessor memo7 o5)
                    (ntp4vc_ttm_cursor scur)
                    (ntp4vc_ttm_accessor memo7 NTP4VC_TTM_Parent
                      (ntp4vc_ttm_cursor scur)))
              ==>
              (let o6 = NTP4VC_TTM_Parent in
               ~(ntp4vc_ttm_cursor scur = null) /\
               (!memo9:A ntp4vc_ttm_memory.
                  ntp4vc_ttm_mark memo9 = ntp4vc_ttm_mark memo8
                  ==>
                  ntp4vc_ttm_accessor memo9 =
                    ntp4vc_ttm_update (ntp4vc_ttm_accessor memo8) o6
                      (ntp4vc_ttm_update
                        (ntp4vc_ttm_accessor memo8 o6)
                        (ntp4vc_ttm_cursor scur)
                        (ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Left
                          (ntp4vc_ttm_cursor scur)))
                  ==>
                  (!o7:A ntp4vc_ttm_snap.
                     ntp4vc_ttm_snapshot memo9
                       (ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Left
                         (ntp4vc_ttm_cursor scur))
                       (ntp4vc_ttm_cursor scur) o7
                     ==>
                     ntp4vc_ttm_transition_post null t stop scur st1
                       memo9 o7
                       (ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Left
                         (ntp4vc_ttm_cursor scur))
                       (ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Left
                         (ntp4vc_ttm_cursor scur) = null))))))))`;;

let ntp4vc_ttm_after_mark = new_definition
 `ntp4vc_ttm_after_mark
    (null:A)
    (t:A ntp4vc_ttm_tree)
    (stop:A ntp4vc_ttm_snap)
    (st1:A ntp4vc_ttm_stack)
    (scur:A ntp4vc_ttm_snap)
    (memo6:A ntp4vc_ttm_memory) <=>
    ~(ntp4vc_ttm_cursor scur = null) /\
    (let o2 =
       ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Left
         (ntp4vc_ttm_cursor scur) in
     (o2 = null ==> ~(ntp4vc_ttm_cursor scur = null)) /\
     (!o3:bool.
        (if o2 = null then
           o3 =
             (if
                ntp4vc_ttm_accessor memo6 NTP4VC_TTM_Right
                  (ntp4vc_ttm_cursor scur) = null
              then T else F)
         else
           o3 = F)
        ==>
        ntp4vc_ttm_leaf_or_rotate null t stop st1 scur memo6 o3))`;;

let ntp4vc_ttm_nonnull_case = new_definition
 `ntp4vc_ttm_nonnull_case
    (null:A)
    (t:A ntp4vc_ttm_tree)
    (stop:A ntp4vc_ttm_snap)
    (st1:A ntp4vc_ttm_stack)
    (scur:A ntp4vc_ttm_snap)
    (memo5:A ntp4vc_ttm_memory) <=>
    ~(ntp4vc_ttm_cursor scur = null) /\
    (!memo6:A ntp4vc_ttm_memory.
       ntp4vc_ttm_accessor memo6 = ntp4vc_ttm_accessor memo5
       ==>
       ntp4vc_ttm_mark memo6 =
         ntp4vc_ttm_update (ntp4vc_ttm_mark memo5)
           (ntp4vc_ttm_cursor scur) T
       ==>
       ntp4vc_ttm_after_mark null t stop st1 scur memo6)`;;

let ntp4vc_ttm_final_case = new_definition
 `ntp4vc_ttm_final_case
    (null:A)
    (memo:A ntp4vc_ttm_memory)
    (t:A ntp4vc_ttm_tree)
    (root:A)
    (stop:A ntp4vc_ttm_snap)
    (st1:A ntp4vc_ttm_stack)
    (memo5:A ntp4vc_ttm_memory) <=>
    st1 = NTP4VC_TTM_Done /\
    (st1 = NTP4VC_TTM_Done
     ==>
     (let o2 = null in
      let o3 = ntp4vc_ttm_pointers stop in
      (ntp4vc_ttm_ext (ntp4vc_ttm_footprint t) o3
         (ntp4vc_ttm_accessor memo5) /\
       ntp4vc_ttm_is_tree null o3 t root o2) /\
      (ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo5)
         t root o2
       ==>
       ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo5)
         t root null /\
       ntp4vc_ttm_unchanged
         (ntp4vc_ttm_accessor memo) (ntp4vc_ttm_accessor memo5) /\
       ntp4vc_ttm_was_marked t
         (ntp4vc_ttm_mark memo) (ntp4vc_ttm_mark memo5))))`;;

let ntp4vc_ttm_iteration_post = new_definition
 `ntp4vc_ttm_iteration_post
    (null:A)
    (memo:A ntp4vc_ttm_memory)
    (t:A ntp4vc_ttm_tree)
    (root:A)
    (stop:A ntp4vc_ttm_snap)
    (entered:bool)
    (st1:A ntp4vc_ttm_stack)
    (scur:A ntp4vc_ttm_snap)
    (memo5:A ntp4vc_ttm_memory) <=>
    (!result:bool.
       (if entered = T then
          result =
            (if ntp4vc_ttm_cursor scur = null then T else F)
        else
          result = F)
       ==>
       (result = T <=> ntp4vc_ttm_cursor scur = null)) /\
    (if ~(ntp4vc_ttm_cursor scur = null) then
       ntp4vc_ttm_nonnull_case null t stop st1 scur memo5
     else
       ntp4vc_ttm_final_case null memo t root stop st1 memo5)`;;

let statement =
 `!null:A.
  !memo:A ntp4vc_ttm_memory.
  !t:A ntp4vc_ttm_tree.
  !root:A.
    ntp4vc_ttm_is_tree null (ntp4vc_ttm_accessor memo)
      t root null /\
    ~(root = null)
    ==>
    !stop:A ntp4vc_ttm_snap.
      ntp4vc_ttm_initial_snap null memo root stop
      ==>
      (ntp4vc_ttm_is_stack null t stop stop
         (NTP4VC_TTM_Bottom:A ntp4vc_ttm_stack) (SOME t) /\
       ntp4vc_ttm_is_tree null (ntp4vc_ttm_pointers stop)
         t (ntp4vc_ttm_cursor stop) (ntp4vc_ttm_parent stop) /\
       ~(ntp4vc_ttm_cursor stop = null)) /\
      (!st:A ntp4vc_ttm_stack.
         ntp4vc_ttm_is_stack null t stop stop st NONE /\
         ntp4vc_ttm_stack_size st <=
           ntp4vc_ttm_stack_size
             (NTP4VC_TTM_Bottom:A ntp4vc_ttm_stack) +
           (&100:int) * ntp4vc_ttm_size t
         ==>
         (~(root = null) /\
          ntp4vc_ttm_initial_snap null memo root stop /\
          ntp4vc_ttm_is_stack null t stop stop st NONE) /\
         (!entered:bool.
          !st1:A ntp4vc_ttm_stack.
          !scur:A ntp4vc_ttm_snap.
          !memo5:A ntp4vc_ttm_memory.
            (ntp4vc_ttm_cursor scur = null ==> entered = T) /\
            ntp4vc_ttm_pointers scur = ntp4vc_ttm_accessor memo5 /\
            ntp4vc_ttm_marks scur = ntp4vc_ttm_mark memo5 /\
            ntp4vc_ttm_is_stack null t stop scur st1 NONE
            ==>
            ntp4vc_ttm_iteration_post
              null memo t root stop entered st1 scur memo5))`;;
