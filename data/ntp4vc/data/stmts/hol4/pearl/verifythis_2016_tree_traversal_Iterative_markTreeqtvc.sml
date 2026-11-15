(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2016_tree_traversal_Iterative_markTreeqtvc: the main
  iterative Morris-style binary-tree marking verification condition, including
  tree shape, snapshots, simulated call stacks, pointer rotations, marking,
  and termination measures. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory optionTheory;

Datatype:
  marktree_kind =
    MarkTreeParent
  | MarkTreeLeft
  | MarkTreeRight
End

Datatype:
  marktree_tree =
    MarkTreeEmpty
  | MarkTreeNode marktree_tree 'loc marktree_tree
End

Datatype:
  marktree_phase =
    MarkTreeGoLeft
  | MarkTreeGoRight
  | MarkTreeGoBack
  | MarkTreeFinish
End

Datatype:
  marktree_memory =
    MarkTreeMemory
      (marktree_kind -> 'loc -> 'loc)
      ('loc -> bool)
End

val marktree_accessor_def = Define `
  marktree_accessor (MarkTreeMemory accessor mark) = accessor`;

val marktree_mark_def = Define `
  marktree_mark (MarkTreeMemory accessor mark) = mark`;

val marktree_update_def = Define `
  marktree_update f x y = \z. if z = x then y else f z`;

val marktree_is_tree_def = Define `
  (marktree_is_tree null memo
      (MarkTreeEmpty : 'loc marktree_tree) c p <=>
     c = null) /\
  (marktree_is_tree null memo (MarkTreeNode l m r) c p <=>
     ~(c = null) /\
     c = m /\
     memo MarkTreeParent c = p /\
     (let cl = memo MarkTreeLeft c
      in
      let cr = memo MarkTreeRight c
      in
        (cl = null <=> cr = null) /\
        marktree_is_tree null memo l cl c /\
        marktree_is_tree null memo r cr c))`;

val marktree_footprint_def = Define `
  (marktree_footprint
      (MarkTreeEmpty : 'loc marktree_tree) x = F) /\
  (marktree_footprint (MarkTreeNode l m r) x =
     (x = m \/
      marktree_footprint l x \/
      marktree_footprint r x))`;

val marktree_ext_def = Define `
  marktree_ext s memo1 memo2 <=>
    !k x. s x ==> memo1 k x = memo2 k x`;

val marktree_unchanged_def = Define `
  marktree_unchanged memo1 memo2 <=>
    !k x. memo1 k x = memo2 k x`;

val marktree_was_marked_def = Define `
  marktree_was_marked t memo1 memo2 <=>
    (!l. marktree_footprint t l ==> memo2 l = T) /\
    (!l. ~marktree_footprint t l ==> memo2 l = memo1 l)`;

val marktree_next_phase_def = Define `
  (marktree_next_phase MarkTreeGoLeft = MarkTreeGoRight) /\
  (marktree_next_phase MarkTreeGoRight = MarkTreeGoBack) /\
  (marktree_next_phase MarkTreeGoBack = MarkTreeGoLeft) /\
  (marktree_next_phase MarkTreeFinish = MarkTreeFinish)`;

val marktree_rotated_def = Define `
  marktree_rotated null memo1 memo2 ph c <=>
    (!k x. ~(x = c) ==> memo1 k x = memo2 k x) /\
    (~(ph = MarkTreeFinish) ==> ~(c = null)) /\
    case ph of
      MarkTreeGoLeft =>
        marktree_unchanged memo1 memo2
    | MarkTreeGoRight =>
        memo2 MarkTreeLeft c = memo1 MarkTreeRight c /\
        memo2 MarkTreeRight c = memo1 MarkTreeParent c /\
        memo2 MarkTreeParent c = memo1 MarkTreeLeft c
    | MarkTreeGoBack =>
        memo1 MarkTreeLeft c = memo2 MarkTreeRight c /\
        memo1 MarkTreeRight c = memo2 MarkTreeParent c /\
        memo1 MarkTreeParent c = memo2 MarkTreeLeft c
    | MarkTreeFinish =>
        c = null`;

Datatype:
  marktree_snap =
    MarkTreeSnap
      (marktree_kind -> 'loc -> 'loc)
      'loc
      'loc
      ('loc -> bool)
End

val marktree_pointers_def = Define `
  marktree_pointers (MarkTreeSnap pointers cursor parent marks) =
    pointers`;

val marktree_cursor_def = Define `
  marktree_cursor (MarkTreeSnap pointers cursor parent marks) =
    cursor`;

val marktree_parent_def = Define `
  marktree_parent (MarkTreeSnap pointers cursor parent marks) =
    parent`;

val marktree_marks_def = Define `
  marktree_marks (MarkTreeSnap pointers cursor parent marks) =
    marks`;

Datatype:
  marktree_frame =
    MarkTreeFrame
      ('loc marktree_snap)
      ('loc marktree_tree)
      ('loc marktree_tree)
      'loc
      ('loc marktree_tree)
      'loc
      ('loc marktree_snap)
      ('loc marktree_snap)
      ('loc marktree_snap)
      ('loc marktree_snap)
End

val marktree_memo0_def = Define `
  marktree_memo0
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = memo0`;

val marktree_frame_tree_def = Define `
  marktree_frame_tree
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = tree`;

val marktree_tleft_def = Define `
  marktree_tleft
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = tleft`;

val marktree_pleft_def = Define `
  marktree_pleft
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = pleft`;

val marktree_tright_def = Define `
  marktree_tright
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = tright`;

val marktree_pright_def = Define `
  marktree_pright
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = pright`;

val marktree_memo1_def = Define `
  marktree_memo1
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = memo1`;

val marktree_memo2_def = Define `
  marktree_memo2
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = memo2`;

val marktree_memo3_def = Define `
  marktree_memo3
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = memo3`;

val marktree_memo4_def = Define `
  marktree_memo4
    (MarkTreeFrame memo0 tree tleft pleft tright pright
       memo1 memo2 memo3 memo4) = memo4`;

val marktree_frame_memo_def = Define `
  marktree_frame_memo f pc =
    if pc <= (0 : int) then marktree_memo0 f
    else if pc <= (1 : int) then marktree_memo1 f
    else if pc <= (2 : int) then marktree_memo2 f
    else if pc <= (3 : int) then marktree_memo3 f
    else marktree_memo4 f`;

val marktree_bloc_rel_def = Define `
  marktree_bloc_rel null mem0 ph s1 s2 <=>
    marktree_parent s2 = marktree_cursor s1 /\
    marktree_cursor s2 =
      marktree_pointers s2 MarkTreeParent (marktree_parent s2) /\
    marktree_marks s2 (marktree_parent s2) = T /\
    (!l.
       ~(l = marktree_parent s2) ==>
       marktree_marks s2 l = marktree_marks s1 l) /\
    if
      marktree_pointers s1 MarkTreeLeft (marktree_cursor s1) = null /\
      null =
        marktree_pointers s1 MarkTreeRight (marktree_cursor s1)
    then
      marktree_pointers s2 = marktree_pointers s1
    else
      marktree_rotated null mem0 (marktree_pointers s2)
        (marktree_next_phase ph) (marktree_parent s2)`;

val marktree_rec_rel_def = Define `
  marktree_rec_rel t s1 s2 <=>
    marktree_unchanged
      (marktree_pointers s1) (marktree_pointers s2) /\
    marktree_cursor s2 = marktree_parent s1 /\
    marktree_parent s2 = marktree_cursor s1 /\
    marktree_was_marked t
      (marktree_marks s1) (marktree_marks s2)`;

Datatype:
  marktree_stack =
    MarkTreeBottom
  | MarkTreeRunning marktree_stack int ('loc marktree_frame)
  | MarkTreeDone
End

val marktree_is_stack_def = Define `
  (marktree_is_stack null t stop scur MarkTreeBottom calls <=>
     stop = scur /\ calls = SOME t) /\
  (marktree_is_stack null t stop scur
      (MarkTreeRunning s1 pc f) calls <=>
     (0 : int) <= pc /\
     pc <= (4 : int) /\
     (let m0 = marktree_memo0 f
      in
        marktree_is_stack null t stop m0 s1
          (SOME (marktree_frame_tree f)) /\
        ~(marktree_cursor m0 = null) /\
        marktree_is_tree null (marktree_pointers m0)
          (marktree_frame_tree f)
          (marktree_cursor m0) (marktree_parent m0) /\
        marktree_frame_tree f =
          MarkTreeNode
            (marktree_tleft f)
            (marktree_cursor m0)
            (marktree_tright f) /\
        marktree_pleft f =
          marktree_pointers m0 MarkTreeLeft (marktree_cursor m0) /\
        marktree_pright f =
          marktree_pointers m0 MarkTreeRight (marktree_cursor m0) /\
        ((1 : int) <= pc ==>
          marktree_bloc_rel null (marktree_pointers m0)
            MarkTreeGoLeft m0 (marktree_memo1 f) /\
          ~(marktree_pleft f = null) /\
          ~(marktree_pright f = null)) /\
        ((2 : int) <= pc ==>
          marktree_rec_rel (marktree_tleft f)
            (marktree_memo1 f) (marktree_memo2 f)) /\
        ((3 : int) <= pc ==>
          marktree_bloc_rel null (marktree_pointers m0)
            MarkTreeGoRight
            (marktree_memo2 f) (marktree_memo3 f)) /\
        ((4 : int) <= pc ==>
          marktree_rec_rel (marktree_tright f)
            (marktree_memo3 f) (marktree_memo4 f)) /\
        marktree_frame_memo f pc = scur /\
        case calls of
          NONE =>
            ~(pc = (1 : int)) /\ ~(pc = (3 : int))
        | SOME u =>
            if pc = (1 : int) then
              u = marktree_tleft f
            else
              pc = (3 : int) /\ u = marktree_tright f)) /\
  (marktree_is_stack null t stop scur MarkTreeDone calls <=>
     marktree_rec_rel t stop scur /\ calls = NONE)`;

val marktree_size_def = Define `
  (marktree_size (MarkTreeEmpty : 'loc marktree_tree) = (0 : int)) /\
  (marktree_size (MarkTreeNode l x r) =
     (1 : int) + marktree_size l + marktree_size r)`;

val marktree_measure_def = Define `
  (marktree_measure
      (MarkTreeBottom : 'loc marktree_stack) = (1 : int)) /\
  (marktree_measure MarkTreeDone = (0 : int)) /\
  (marktree_measure (MarkTreeRunning s pc f) =
     marktree_measure s + ((100 : int) - pc) +
       if pc = (0 : int) then
         (100 : int) *
           (marktree_size (marktree_tleft f) +
            marktree_size (marktree_tright f))
       else if pc <= (2 : int) then
         (100 : int) * marktree_size (marktree_tright f)
       else
         (0 : int))`;

val verifythis_2016_tree_traversal_Iterative_markTree_vc =
  ``!(null : 'loc)
      (memo : 'loc marktree_memory)
      (t : 'loc marktree_tree)
      (root : 'loc).
      marktree_is_tree null (marktree_accessor memo) t root null /\
      ~(root = null) ==>
      let o1 = null
      in
        !stop : 'loc marktree_snap.
          marktree_pointers stop = marktree_accessor memo /\
          marktree_cursor stop = root /\
          marktree_parent stop = o1 /\
          marktree_marks stop = marktree_mark memo ==>
          (marktree_is_stack null t stop stop MarkTreeBottom
             (SOME t) /\
           marktree_is_tree null (marktree_pointers stop) t
             (marktree_cursor stop) (marktree_parent stop) /\
           ~(marktree_cursor stop = null)) /\
          !st : 'loc marktree_stack.
            marktree_is_stack null t stop stop st NONE /\
            marktree_measure st <=
              marktree_measure MarkTreeBottom +
                (100 : int) * marktree_size t ==>
            (~(root = null) /\
             marktree_pointers stop = marktree_accessor memo /\
             marktree_cursor stop = root /\
             marktree_parent stop = o1 /\
             marktree_marks stop = marktree_mark memo /\
             marktree_is_stack null t stop stop st NONE) /\
            !entered : bool.
            !st1 : 'loc marktree_stack.
            !scur : 'loc marktree_snap.
            !memo5 : 'loc marktree_memory.
              (marktree_cursor scur = null ==> entered = T) /\
              marktree_pointers scur = marktree_accessor memo5 /\
              marktree_marks scur = marktree_mark memo5 /\
              marktree_is_stack null t stop scur st1 NONE ==>
              (!result : bool.
                 (if entered = T then
                    result =
                      (if marktree_cursor scur = null then T else F)
                  else
                    result = F) ==>
                 (result = T <=>
                  marktree_cursor scur = null)) /\
              if ~(marktree_cursor scur = null) then
                ~(marktree_cursor scur = null) /\
                !memo6 : 'loc marktree_memory.
                  marktree_accessor memo6 =
                    marktree_accessor memo5 ==>
                  marktree_mark memo6 =
                    marktree_update
                      (marktree_mark memo5)
                      (marktree_cursor scur) T ==>
                  ~(marktree_cursor scur = null) /\
                  (let o2 =
                     marktree_accessor memo6 MarkTreeLeft
                       (marktree_cursor scur)
                   in
                     (o2 = null ==>
                      ~(marktree_cursor scur = null)) /\
                     !o3 : bool.
                       (if o2 = null then
                          o3 =
                            (if
                               marktree_accessor memo6 MarkTreeRight
                                 (marktree_cursor scur) = null
                             then T
                             else F)
                        else
                          o3 = F) ==>
                       if o3 = T then
                         ~(marktree_cursor scur = null) /\
                         !o4 : 'loc marktree_snap.
                           marktree_pointers o4 =
                             marktree_accessor memo6 /\
                           marktree_cursor o4 =
                             marktree_accessor memo6 MarkTreeParent
                               (marktree_cursor scur) /\
                           marktree_parent o4 =
                             marktree_cursor scur /\
                           marktree_marks o4 =
                             marktree_mark memo6 ==>
                           (marktree_is_stack null t stop scur
                              st1 NONE /\
                            (case st1 of
                               MarkTreeBottom => F
                             | MarkTreeDone => F
                             | MarkTreeRunning s pc f =>
                                 marktree_bloc_rel null
                                   (marktree_pointers
                                      (marktree_memo0 f))
                                   (if pc = (0 : int) then
                                      MarkTreeGoLeft
                                    else if pc = (2 : int) then
                                      MarkTreeGoRight
                                    else
                                      MarkTreeGoBack)
                                   scur o4)) /\
                           !st2 : 'loc marktree_stack.
                             marktree_is_stack null t stop o4 st2 NONE /\
                             marktree_measure st2 <
                               marktree_measure st1 ==>
                             ((0 : int) <=
                                marktree_measure st1 /\
                              marktree_measure st2 <
                                marktree_measure st1) /\
                             (marktree_accessor memo6 MarkTreeParent
                                (marktree_cursor scur) = null ==>
                              T) /\
                             marktree_pointers o4 =
                               marktree_accessor memo6 /\
                             marktree_cursor o4 =
                               marktree_accessor memo6 MarkTreeParent
                                 (marktree_cursor scur) /\
                             marktree_parent o4 =
                               marktree_cursor scur /\
                             marktree_marks o4 =
                               marktree_mark memo6 /\
                             marktree_is_stack null t stop o4 st2 NONE
                       else
                         ~(marktree_cursor scur = null) /\
                         ~(marktree_cursor scur = null) /\
                         (let o4 = MarkTreeLeft
                          in
                            ~(marktree_cursor scur = null) /\
                            !memo7 : 'loc marktree_memory.
                              marktree_mark memo7 =
                                marktree_mark memo6 ==>
                              marktree_accessor memo7 =
                                marktree_update
                                  (marktree_accessor memo6) o4
                                  (marktree_update
                                     (marktree_accessor memo6 o4)
                                     (marktree_cursor scur)
                                     (marktree_accessor memo6
                                        MarkTreeRight
                                        (marktree_cursor scur))) ==>
                              ~(marktree_cursor scur = null) /\
                              (let o5 = MarkTreeRight
                               in
                                 ~(marktree_cursor scur = null) /\
                                 !memo8 : 'loc marktree_memory.
                                   marktree_mark memo8 =
                                     marktree_mark memo7 ==>
                                   marktree_accessor memo8 =
                                     marktree_update
                                       (marktree_accessor memo7) o5
                                       (marktree_update
                                          (marktree_accessor memo7 o5)
                                          (marktree_cursor scur)
                                          (marktree_accessor memo7
                                             MarkTreeParent
                                             (marktree_cursor scur))) ==>
                                   (let o6 = MarkTreeParent
                                    in
                                      ~(marktree_cursor scur = null) /\
                                      !memo9 : 'loc marktree_memory.
                                        marktree_mark memo9 =
                                          marktree_mark memo8 ==>
                                        marktree_accessor memo9 =
                                          marktree_update
                                            (marktree_accessor memo8) o6
                                            (marktree_update
                                               (marktree_accessor
                                                  memo8 o6)
                                               (marktree_cursor scur)
                                               (marktree_accessor memo6
                                                  MarkTreeLeft
                                                  (marktree_cursor
                                                     scur))) ==>
                                        !o7 : 'loc marktree_snap.
                                          marktree_pointers o7 =
                                            marktree_accessor memo9 /\
                                          marktree_cursor o7 =
                                            marktree_accessor memo6
                                              MarkTreeLeft
                                              (marktree_cursor scur) /\
                                          marktree_parent o7 =
                                            marktree_cursor scur /\
                                          marktree_marks o7 =
                                            marktree_mark memo9 ==>
                                          (marktree_is_stack null t stop
                                             scur st1 NONE /\
                                           (case st1 of
                                              MarkTreeBottom => F
                                            | MarkTreeDone => F
                                            | MarkTreeRunning s pc f =>
                                                marktree_bloc_rel null
                                                  (marktree_pointers
                                                     (marktree_memo0 f))
                                                  (if
                                                     pc = (0 : int)
                                                   then MarkTreeGoLeft
                                                   else if
                                                     pc = (2 : int)
                                                   then MarkTreeGoRight
                                                   else MarkTreeGoBack)
                                                  scur o7)) /\
                                          !st2 :
                                             'loc marktree_stack.
                                            marktree_is_stack null t stop
                                              o7 st2 NONE /\
                                            marktree_measure st2 <
                                              marktree_measure st1 ==>
                                            ((0 : int) <=
                                               marktree_measure st1 /\
                                             marktree_measure st2 <
                                               marktree_measure st1) /\
                                            (marktree_accessor memo6
                                               MarkTreeLeft
                                               (marktree_cursor scur) =
                                               null ==>
                                             T) /\
                                            marktree_pointers o7 =
                                              marktree_accessor memo9 /\
                                            marktree_cursor o7 =
                                              marktree_accessor memo6
                                                MarkTreeLeft
                                                (marktree_cursor scur) /\
                                            marktree_parent o7 =
                                              marktree_cursor scur /\
                                            marktree_marks o7 =
                                              marktree_mark memo9 /\
                                            marktree_is_stack null t stop
                                              o7 st2 NONE))))
              else
                (case st1 of
                   MarkTreeDone => T
                 | _ => F) /\
                ((case st1 of
                    MarkTreeDone => T
                  | _ => F) ==>
                 (let o2 = null
                  in
                  let o3 = marktree_pointers stop
                  in
                    (marktree_ext (marktree_footprint t) o3
                       (marktree_accessor memo5) /\
                     marktree_is_tree null o3 t root o2) /\
                    (marktree_is_tree null
                       (marktree_accessor memo5) t root o2 ==>
                     marktree_is_tree null
                       (marktree_accessor memo5) t root null /\
                     marktree_unchanged
                       (marktree_accessor memo)
                       (marktree_accessor memo5) /\
                     marktree_was_marked t
                       (marktree_mark memo)
                       (marktree_mark memo5))))``;
