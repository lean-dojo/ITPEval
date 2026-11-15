(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_fuseqtvc: an AVL-tree fusion verification condition
  preserving concatenated sequences and bounding height loss across empty
  and node views. This file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus avl_fuse_t1
  and avl_fuse_t2 are bijective indexed wrappers of their arbitrary underlying
  carriers, preserving the source t1 alpha and t2 alpha families without
  adding or removing data.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_fuse_t1 = AvlFuseT1 ('index -> unit) 'node
End

Datatype:
  avl_fuse_t2 = AvlFuseT2 ('index -> unit) 'carrier
End

Datatype:
  avl_fuse_model_tree =
    AvlFuseModelEmpty
  | AvlFuseModelNode avl_fuse_model_tree
      (('index, 'node) avl_fuse_t1)
      avl_fuse_model_tree num 'summary
End

Datatype:
  avl_fuse_model =
    AvlFuseModel ((('index, 'node) avl_fuse_t1) list) int
End

Datatype:
  avl_fuse_view =
    AvlFuseEmpty
  | AvlFuseNode
      (('carrier, 'index) avl_fuse_t2)
      (('index, 'node) avl_fuse_t1)
      (('carrier, 'index) avl_fuse_t2)
      num 'summary
End

val avl_fuse_model_seq_def = Define `
  avl_fuse_model_seq (AvlFuseModel elements height) = elements`;

val avl_fuse_model_hgt_def = Define `
  avl_fuse_model_hgt (AvlFuseModel elements height) = height`;

val avl_fuse_seq_model_def = Define `
  (avl_fuse_seq_model AvlFuseModelEmpty = []) /\
  (avl_fuse_seq_model
      (AvlFuseModelNode left root right height summary) =
     APPEND (avl_fuse_seq_model left)
       (root :: avl_fuse_seq_model right))`;

val avl_fuse_real_height_def = Define `
  (avl_fuse_real_height AvlFuseModelEmpty = (0 : int)) /\
  (avl_fuse_real_height
      (AvlFuseModelNode left root right height summary) =
     1 +
       (if avl_fuse_real_height left < avl_fuse_real_height right
        then avl_fuse_real_height right
        else avl_fuse_real_height left))`;

val avl_fuse_balanced_def = Define `
  (avl_fuse_balanced balancing agg measure_closure
      AvlFuseModelEmpty = T) /\
  (avl_fuse_balanced balancing agg measure_closure
      (AvlFuseModelNode left root right height summary) =
     (&height =
        avl_fuse_real_height
          (AvlFuseModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_fuse_seq_model
            (AvlFuseModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_fuse_real_height right -
        avl_fuse_real_height left /\
      avl_fuse_real_height right -
        avl_fuse_real_height left <= &balancing /\
      avl_fuse_balanced balancing agg measure_closure left /\
      avl_fuse_balanced balancing agg measure_closure right))`;

val avl_fuse_vc =
  ``let node_model =
      \left : (('index, 'node) avl_fuse_t1) list.
      \root : ('index, 'node) avl_fuse_t1.
      \right : (('index, 'node) avl_fuse_t1) list.
        APPEND left (root :: right)
    in
    let expected_height =
      \left_height : int. \right_height : int.
        1 +
          (if left_height < right_height
           then right_height
           else left_height)
    in
    let within_balance =
      \balancing : num. \left_height : int. \right_height : int.
        -(&balancing) <= left_height - right_height /\
        left_height - right_height <= &balancing
    in
    let one_step_height_loss =
      \expected : int. \actual : int.
        (0 : int) <= expected - actual /\
        expected - actual <= 1
    in
    let view_ok =
      \balancing : num.
      \agg :
        ((('index, 'node) avl_fuse_t1) -> 'summary) ->
        (('index, 'node) avl_fuse_t1) list -> 'summary.
      \measure_closure :
        (('index, 'node) avl_fuse_t1) -> 'summary.
      \seq :
        (('carrier, 'index) avl_fuse_t2) ->
        (('index, 'node) avl_fuse_t1) list.
      \hgt : (('carrier, 'index) avl_fuse_t2) -> int.
      \whole : ('carrier, 'index) avl_fuse_t2.
      \v : ('carrier, 'index, 'node, 'summary) avl_fuse_view.
        case v of
          AvlFuseEmpty =>
            hgt whole = 0 /\
            seq whole = []
        | AvlFuseNode left root right height summary =>
            seq whole =
              node_model (seq left) root (seq right) /\
            summary = agg measure_closure (seq whole) /\
            within_balance balancing (hgt left) (hgt right) /\
            hgt whole = &height /\
            &height = expected_height (hgt left) (hgt right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg :
        ((('index, 'node) avl_fuse_t1) -> 'summary) ->
        (('index, 'node) avl_fuse_t1) list -> 'summary)
      (measure : (('index, 'node) avl_fuse_t1) -> 'summary)
      (measure_closure :
        (('index, 'node) avl_fuse_t1) -> 'summary)
      (repr :
        (('carrier, 'index) avl_fuse_t2) ->
        ('index, 'node, 'summary) avl_fuse_model_tree)
      (m1 :
        (('carrier, 'index) avl_fuse_t2) ->
        ('index, 'node) avl_fuse_model)
      (l : ('carrier, 'index) avl_fuse_t2)
      (r : ('carrier, 'index) avl_fuse_t2)
      (o1 : ('carrier, 'index, 'node, 'summary) avl_fuse_view).
      (0 : int) < &balancing ==>
      (!a b c. op a (op b c) = op (op a b) c) ==>
      (!x. op x zero = x /\ x = op zero x) ==>
      (!f. agg f [] = zero) ==>
      (!s f.
         LENGTH s = 1 ==>
         agg f s = f (EL 0 s)) ==>
      (!f s1 s2.
         agg f (APPEND s1 s2) =
         op (agg f s1) (agg f s2)) ==>
      (!y. measure_closure y = measure y) ==>
      (!self.
         avl_fuse_balanced balancing agg measure_closure
           (repr self) /\
         avl_fuse_model_seq (m1 self) =
           avl_fuse_seq_model (repr self) /\
         avl_fuse_model_hgt (m1 self) =
           avl_fuse_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      -(&balancing) <=
        avl_fuse_model_hgt (m1 l) -
        avl_fuse_model_hgt (m1 r) ==>
      avl_fuse_model_hgt (m1 l) -
        avl_fuse_model_hgt (m1 r) <= &balancing ==>
      view_ok balancing agg measure_closure
        avl_fuse_model_seq avl_fuse_model_hgt l o1
      ==>
      ((case o1 of
          AvlFuseEmpty => T
        | AvlFuseNode left root right height summary =>
            !o2 : ('carrier, 'index, 'node, 'summary) avl_fuse_view.
              view_ok balancing agg measure_closure
                avl_fuse_model_seq avl_fuse_model_hgt r o2
              ==>
              case o2 of
                AvlFuseEmpty => T
              | AvlFuseNode right_left right_root right_right
                  right_height right_summary =>
                  within_balance balancing
                    (avl_fuse_model_hgt (m1 right_left))
                    (avl_fuse_model_hgt (m1 right_right)) /\
                  !new_root : ('index, 'node) avl_fuse_t1.
                  !new_right : ('carrier, 'index) avl_fuse_t2.
                    (node_model
                       (avl_fuse_model_seq (m1 right_left))
                       right_root
                       (avl_fuse_model_seq (m1 right_right)) =
                       new_root ::
                         avl_fuse_model_seq (m1 new_right) /\
                     one_step_height_loss
                       (expected_height
                         (avl_fuse_model_hgt (m1 right_left))
                         (avl_fuse_model_hgt (m1 right_right)))
                       (avl_fuse_model_hgt (m1 new_right)))
                    ==>
                    -(&balancing) - 1 <=
                      avl_fuse_model_hgt (m1 l) -
                      avl_fuse_model_hgt (m1 new_right) /\
                    avl_fuse_model_hgt (m1 l) -
                      avl_fuse_model_hgt (m1 new_right) <=
                      &balancing + 1) /\
       !result : ('carrier, 'index) avl_fuse_t2.
         (case o1 of
            AvlFuseEmpty =>
              result = r
          | AvlFuseNode left root right height summary =>
              ?o2 : ('carrier, 'index, 'node, 'summary) avl_fuse_view.
                view_ok balancing agg measure_closure
                  avl_fuse_model_seq avl_fuse_model_hgt r o2 /\
                case o2 of
                  AvlFuseEmpty =>
                    result = l
                | AvlFuseNode right_left right_root right_right
                    right_height right_summary =>
                    ?new_root : ('index, 'node) avl_fuse_t1.
                    ?new_right : ('carrier, 'index) avl_fuse_t2.
                      (node_model
                         (avl_fuse_model_seq (m1 right_left))
                         right_root
                         (avl_fuse_model_seq (m1 right_right)) =
                         new_root ::
                           avl_fuse_model_seq (m1 new_right) /\
                       one_step_height_loss
                         (expected_height
                           (avl_fuse_model_hgt (m1 right_left))
                           (avl_fuse_model_hgt (m1 right_right)))
                         (avl_fuse_model_hgt (m1 new_right))) /\
                      avl_fuse_model_seq (m1 result) =
                        node_model
                          (avl_fuse_model_seq (m1 l))
                          new_root
                          (avl_fuse_model_seq (m1 new_right)) /\
                      (one_step_height_loss
                         (expected_height
                           (avl_fuse_model_hgt (m1 l))
                           (avl_fuse_model_hgt (m1 new_right)))
                         (avl_fuse_model_hgt (m1 result)) /\
                       (within_balance balancing
                          (avl_fuse_model_hgt (m1 l))
                          (avl_fuse_model_hgt (m1 new_right))
                        ==>
                        expected_height
                          (avl_fuse_model_hgt (m1 l))
                          (avl_fuse_model_hgt (m1 new_right)) =
                        avl_fuse_model_hgt (m1 result))))
         ==>
         avl_fuse_model_seq (m1 result) =
           APPEND
             (avl_fuse_model_seq (m1 l))
             (avl_fuse_model_seq (m1 r)) /\
         (expected_height
            (avl_fuse_model_hgt (m1 l))
            (avl_fuse_model_hgt (m1 r)) -
            avl_fuse_model_hgt (m1 result) <= 1 /\
          (0 : int) <=
            expected_height
              (avl_fuse_model_hgt (m1 l))
              (avl_fuse_model_hgt (m1 r)) -
            avl_fuse_model_hgt (m1 result)))``;
