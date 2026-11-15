(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2016_tree_traversal_Recursive_markTreeqtvc: the recursive
  Morris-style binary-tree marking verification condition, including pointer
  rotations, recursive subtree traversal, restoration of tree shape, and
  marking of every tree node. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;

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

val verifythis_2016_tree_traversal_Recursive_markTree_vc =
  ``!(null : 'loc)
      (memo : 'loc marktree_memory)
      (t : 'loc marktree_tree)
      (root : 'loc).
      marktree_is_tree null (marktree_accessor memo) t root null /\
      ~(root = null) ==>
      let o1 = null
      in
        (!entered : bool.
         !x : 'loc.
         !memo1 : 'loc marktree_memory.
         !mem0 : marktree_kind -> 'loc -> 'loc.
         !ph : marktree_phase.
           marktree_rotated null mem0
             (marktree_accessor memo1) ph x /\
           (ph = MarkTreeFinish ==> entered = T) ==>
           !o2 : bool.
             (if entered = T then
                o2 = (if x = null then T else F)
              else
                o2 = F) ==>
             if o2 = T then
               ph = MarkTreeFinish
             else
               ~(x = null) /\
               !memo2 : 'loc marktree_memory.
                 marktree_accessor memo2 =
                   marktree_accessor memo1 ==>
                 marktree_mark memo2 =
                   marktree_update (marktree_mark memo1) x T ==>
                 ~(x = null) /\
                 (let o3 =
                    marktree_accessor memo2 MarkTreeLeft x
                  in
                    (o3 = null ==> ~(x = null)) /\
                    !o4 : bool.
                      (if o3 = null then
                         o4 =
                           (if
                              marktree_accessor memo2 MarkTreeRight x =
                                null
                            then T
                            else F)
                       else
                         o4 = F) ==>
                      if o4 = T then
                        ~(x = null) /\
                        ~(ph = MarkTreeFinish) /\
                        marktree_mark memo2 x = T /\
                        (!l : 'loc.
                           ~(l = x) ==>
                           marktree_mark memo2 l =
                             marktree_mark memo1 l) /\
                        (if
                           marktree_accessor memo1 MarkTreeLeft x =
                             null /\
                           null =
                             marktree_accessor memo1 MarkTreeRight x
                         then
                           marktree_accessor memo2 =
                             marktree_accessor memo1
                         else
                           marktree_rotated null mem0
                             (marktree_accessor memo2)
                             (marktree_next_phase ph) x)
                      else
                        ~(x = null) /\
                        ~(x = null) /\
                        (let o5 = MarkTreeLeft
                         in
                           ~(x = null) /\
                           !memo3 : 'loc marktree_memory.
                             marktree_mark memo3 =
                               marktree_mark memo2 ==>
                             marktree_accessor memo3 =
                               marktree_update
                                 (marktree_accessor memo2) o5
                                 (marktree_update
                                    (marktree_accessor memo2 o5) x
                                    (marktree_accessor memo2
                                       MarkTreeRight x)) ==>
                             ~(x = null) /\
                             (let o6 = MarkTreeRight
                              in
                                ~(x = null) /\
                                !memo4 : 'loc marktree_memory.
                                  marktree_mark memo4 =
                                    marktree_mark memo3 ==>
                                  marktree_accessor memo4 =
                                    marktree_update
                                      (marktree_accessor memo3) o6
                                      (marktree_update
                                         (marktree_accessor memo3 o6) x
                                         (marktree_accessor memo3
                                            MarkTreeParent x)) ==>
                                  (let o7 = MarkTreeParent
                                   in
                                     ~(x = null) /\
                                     !memo5 :
                                        'loc marktree_memory.
                                       marktree_mark memo5 =
                                         marktree_mark memo4 ==>
                                       marktree_accessor memo5 =
                                         marktree_update
                                           (marktree_accessor memo4) o7
                                           (marktree_update
                                              (marktree_accessor
                                                 memo4 o7) x
                                              (marktree_accessor memo2
                                                 MarkTreeLeft x)) ==>
                                       marktree_accessor memo2
                                           MarkTreeLeft x =
                                         marktree_accessor memo5
                                           MarkTreeParent x /\
                                       ~(ph = MarkTreeFinish) /\
                                       marktree_mark memo5 x = T /\
                                       (!l : 'loc.
                                          ~(l = x) ==>
                                          marktree_mark memo5 l =
                                            marktree_mark memo1 l) /\
                                       (if
                                          marktree_accessor memo1
                                              MarkTreeLeft x = null /\
                                          null =
                                            marktree_accessor memo1
                                              MarkTreeRight x
                                        then
                                          marktree_accessor memo5 =
                                            marktree_accessor memo1
                                        else
                                          marktree_rotated null mem0
                                            (marktree_accessor memo5)
                                            (marktree_next_phase ph)
                                            x)))))) /\
        (!z : 'loc.
         !x : 'loc.
         !memo1 : 'loc marktree_memory.
         !t1 : 'loc marktree_tree.
           ~(x = null) /\
           marktree_is_tree null (marktree_accessor memo1)
             t1 x z ==>
           (let mem0 = marktree_accessor memo1
            in
              ~(x = null) /\
              (let x_lf =
                 marktree_accessor memo1 MarkTreeLeft x
               in
                 ~(x = null) /\
                 (let x_rg =
                    marktree_accessor memo1 MarkTreeRight x
                  in
                    (case t1 of
                       MarkTreeEmpty => F
                     | MarkTreeNode l m r => T) /\
                    !lf : 'loc marktree_tree.
                    !rg : 'loc marktree_tree.
                      (case t1 of
                         MarkTreeEmpty => F
                       | MarkTreeNode l m r =>
                           lf = l /\ rg = r) ==>
                      marktree_is_tree null mem0
                        (MarkTreeNode lf x rg) x z /\
                      (~marktree_footprint lf x /\
                       ~marktree_footprint rg x ==>
                       (let o2 = MarkTreeGoLeft
                        in
                          marktree_rotated null mem0
                            (marktree_accessor memo1) o2 x /\
                          !memo2 : 'loc marktree_memory.
                            marktree_mark memo2 x = T /\
                            (!l : 'loc.
                               ~(l = x) ==>
                               marktree_mark memo2 l =
                                 marktree_mark memo1 l) /\
                            (if
                               marktree_accessor memo1
                                   MarkTreeLeft x = null /\
                               null =
                                 marktree_accessor memo1
                                   MarkTreeRight x
                             then
                               marktree_accessor memo2 =
                                 marktree_accessor memo1
                             else
                               marktree_rotated null mem0
                                 (marktree_accessor memo2)
                                 (marktree_next_phase o2) x) ==>
                            (!result : bool.
                               (if x_lf = null then
                                  result =
                                    (if x_rg = null then T else F)
                                else
                                  result = F) ==>
                               (result = T <=>
                                x_lf = null /\ x_rg = null) /\
                               (result = T ==>
                                lf =
                                  (MarkTreeEmpty :
                                     'loc marktree_tree) /\
                                rg =
                                  (MarkTreeEmpty :
                                     'loc marktree_tree))) /\
                            ((x_lf = null /\ x_rg = null ==>
                              lf =
                                (MarkTreeEmpty :
                                   'loc marktree_tree) /\
                              rg =
                                (MarkTreeEmpty :
                                   'loc marktree_tree)) ==>
                             if
                               ~(x_lf = null /\ x_rg = null)
                             then
                               (marktree_ext
                                  (marktree_footprint lf) mem0
                                  (marktree_accessor memo2) /\
                                marktree_is_tree null mem0 lf
                                  x_lf x) /\
                               (marktree_is_tree null
                                  (marktree_accessor memo2)
                                  lf x_lf x ==>
                                (case t1 of
                                   MarkTreeEmpty => F
                                 | MarkTreeNode f m f1 =>
                                     f = lf \/ f1 = lf) /\
                                ~(marktree_accessor memo2
                                    MarkTreeParent x = null) /\
                                marktree_is_tree null
                                  (marktree_accessor memo2) lf
                                  (marktree_accessor memo2
                                     MarkTreeParent x) x /\
                                !memo3 : 'loc marktree_memory.
                                  marktree_unchanged
                                      (marktree_accessor memo2)
                                      (marktree_accessor memo3) /\
                                  marktree_was_marked lf
                                      (marktree_mark memo2)
                                      (marktree_mark memo3) ==>
                                  (let o3 = MarkTreeGoRight
                                   in
                                     marktree_rotated null mem0
                                       (marktree_accessor memo3)
                                       o3 x /\
                                     !memo4 :
                                        'loc marktree_memory.
                                       marktree_mark memo4 x = T /\
                                       (!l : 'loc.
                                          ~(l = x) ==>
                                          marktree_mark memo4 l =
                                            marktree_mark memo3 l) /\
                                       (if
                                          marktree_accessor memo3
                                              MarkTreeLeft x = null /\
                                          null =
                                            marktree_accessor memo3
                                              MarkTreeRight x
                                        then
                                          marktree_accessor memo4 =
                                            marktree_accessor memo3
                                        else
                                          marktree_rotated null mem0
                                            (marktree_accessor memo4)
                                            (marktree_next_phase o3)
                                            x) ==>
                                       (marktree_ext
                                          (marktree_footprint rg)
                                          mem0
                                          (marktree_accessor memo4) /\
                                        marktree_is_tree null mem0 rg
                                          x_rg x) /\
                                       (marktree_is_tree null
                                          (marktree_accessor memo4)
                                          rg x_rg x ==>
                                        (case t1 of
                                           MarkTreeEmpty => F
                                         | MarkTreeNode f m f1 =>
                                             f = rg \/ f1 = rg) /\
                                        ~(marktree_accessor memo4
                                            MarkTreeParent x = null) /\
                                        marktree_is_tree null
                                          (marktree_accessor memo4) rg
                                          (marktree_accessor memo4
                                             MarkTreeParent x) x /\
                                        !memo5 :
                                           'loc marktree_memory.
                                          marktree_unchanged
                                              (marktree_accessor memo4)
                                              (marktree_accessor memo5) /\
                                          marktree_was_marked rg
                                              (marktree_mark memo4)
                                              (marktree_mark memo5) ==>
                                          (let o4 = MarkTreeGoBack
                                           in
                                             marktree_rotated null mem0
                                               (marktree_accessor memo5)
                                               o4 x /\
                                             !memo6 :
                                                'loc marktree_memory.
                                               marktree_mark memo6 x =
                                                 T /\
                                               (!l : 'loc.
                                                  ~(l = x) ==>
                                                  marktree_mark memo6 l =
                                                    marktree_mark
                                                      memo5 l) /\
                                               (if
                                                  marktree_accessor
                                                      memo5
                                                      MarkTreeLeft x =
                                                    null /\
                                                  null =
                                                    marktree_accessor
                                                      memo5
                                                      MarkTreeRight x
                                                then
                                                  marktree_accessor
                                                      memo6 =
                                                    marktree_accessor
                                                      memo5
                                                else
                                                  marktree_rotated null
                                                    mem0
                                                    (marktree_accessor
                                                       memo6)
                                                    (marktree_next_phase
                                                       o4) x) ==>
                                               marktree_unchanged
                                                 (marktree_accessor
                                                    memo1)
                                                 (marktree_accessor
                                                    memo6) /\
                                               marktree_accessor memo6
                                                   MarkTreeParent x = z /\
                                               marktree_was_marked t1
                                                 (marktree_mark memo1)
                                                 (marktree_mark
                                                    memo6)))))
                             else
                               marktree_unchanged
                                 (marktree_accessor memo1)
                                 (marktree_accessor memo2) /\
                               marktree_accessor memo2
                                   MarkTreeParent x = z /\
                               marktree_was_marked t1
                                 (marktree_mark memo1)
                                 (marktree_mark memo2)))))))) /\
        (let mem0 = marktree_accessor memo
         in
           (~(root = null) /\
            marktree_is_tree null (marktree_accessor memo)
              t root o1) /\
           !memo1 : 'loc marktree_memory.
             marktree_unchanged (marktree_accessor memo)
                 (marktree_accessor memo1) /\
             marktree_was_marked t
                 (marktree_mark memo)
                 (marktree_mark memo1) ==>
             marktree_rotated null mem0
               (marktree_accessor memo1) MarkTreeFinish o1 /\
             !x : 'loc.
               marktree_rotated null mem0
                 (marktree_accessor memo1) MarkTreeFinish x ==>
               marktree_rotated null mem0
                 (marktree_accessor memo1) MarkTreeFinish x /\
               (let o2 = null
                in
                  (marktree_ext (marktree_footprint t) mem0
                     (marktree_accessor memo1) /\
                   marktree_is_tree null mem0 t root o2) /\
                  (marktree_is_tree null
                     (marktree_accessor memo1) t root o2 ==>
                   marktree_is_tree null
                     (marktree_accessor memo1) t root null /\
                   marktree_unchanged
                     (marktree_accessor memo)
                     (marktree_accessor memo1) /\
                   marktree_was_marked t
                     (marktree_mark memo)
                     (marktree_mark memo1))))``;
