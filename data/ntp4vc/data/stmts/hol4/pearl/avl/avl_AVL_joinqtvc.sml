(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_joinqtvc: an AVL-tree join verification condition
  preserving the concatenated in-order sequence and bounding height loss
  across empty and node views. This file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus avl_join_t1
  and avl_join_t2 are bijective indexed wrappers of their arbitrary underlying
  carriers, preserving the source t1 alpha and t2 alpha families without
  adding or removing data.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_join_t1 = AvlJoinT1 ('index -> unit) 'node
End

Datatype:
  avl_join_t2 = AvlJoinT2 ('index -> unit) 'carrier
End

Datatype:
  avl_join_model_tree =
    AvlJoinModelEmpty
  | AvlJoinModelNode avl_join_model_tree
      (('index, 'node) avl_join_t1)
      avl_join_model_tree num 'summary
End

Datatype:
  avl_join_model =
    AvlJoinModel ((('index, 'node) avl_join_t1) list) int
End

Datatype:
  avl_join_view =
    AvlJoinEmpty
  | AvlJoinNode
      (('index, 'carrier) avl_join_t2)
      (('index, 'node) avl_join_t1)
      (('index, 'carrier) avl_join_t2)
      num 'summary
End

val avl_join_model_seq_def = Define `
  avl_join_model_seq (AvlJoinModel elements height) = elements`;

val avl_join_model_hgt_def = Define `
  avl_join_model_hgt (AvlJoinModel elements height) = height`;

val avl_join_seq_model_def = Define `
  (avl_join_seq_model AvlJoinModelEmpty = []) /\
  (avl_join_seq_model
      (AvlJoinModelNode left root right height summary) =
     APPEND (avl_join_seq_model left)
       (root :: avl_join_seq_model right))`;

val avl_join_real_height_def = Define `
  (avl_join_real_height AvlJoinModelEmpty = (0 : int)) /\
  (avl_join_real_height
      (AvlJoinModelNode left root right height summary) =
     1 +
       (if avl_join_real_height left < avl_join_real_height right
        then avl_join_real_height right
        else avl_join_real_height left))`;

val avl_join_balanced_def = Define `
  (avl_join_balanced balancing agg measure_closure
      AvlJoinModelEmpty = T) /\
  (avl_join_balanced balancing agg measure_closure
      (AvlJoinModelNode left root right height summary) =
     (&height =
        avl_join_real_height
          (AvlJoinModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_join_seq_model
            (AvlJoinModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_join_real_height right -
        avl_join_real_height left /\
      avl_join_real_height right -
        avl_join_real_height left <= &balancing /\
      avl_join_balanced balancing agg measure_closure left /\
      avl_join_balanced balancing agg measure_closure right))`;

val avl_join_vc =
  ``let node_model =
      \left : (('index, 'node) avl_join_t1) list.
      \root : ('index, 'node) avl_join_t1.
      \right : (('index, 'node) avl_join_t1) list.
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
    let height_distance =
      \left_height : int. \right_height : int.
        if right_height < left_height
        then left_height - right_height
        else right_height - left_height
    in
    let built_node =
      \seq :
        (('index, 'carrier) avl_join_t2) ->
        (('index, 'node) avl_join_t1) list.
      \hgt : (('index, 'carrier) avl_join_t2) -> int.
      \out : ('index, 'carrier) avl_join_t2.
      \left : ('index, 'carrier) avl_join_t2.
      \root : ('index, 'node) avl_join_t1.
      \right : ('index, 'carrier) avl_join_t2.
        seq out = node_model (seq left) root (seq right) /\
        one_step_height_loss
          (expected_height (hgt left) (hgt right))
          (hgt out)
    in
    let view_ok =
      \balancing : num.
      \agg :
        ((('index, 'node) avl_join_t1) -> 'summary) ->
        (('index, 'node) avl_join_t1) list -> 'summary.
      \measure_closure :
        (('index, 'node) avl_join_t1) -> 'summary.
      \seq :
        (('index, 'carrier) avl_join_t2) ->
        (('index, 'node) avl_join_t1) list.
      \hgt : (('index, 'carrier) avl_join_t2) -> int.
      \whole : ('index, 'carrier) avl_join_t2.
      \v : ('carrier, 'index, 'node, 'summary) avl_join_view.
        case v of
          AvlJoinEmpty =>
            hgt whole = 0 /\
            seq whole = []
        | AvlJoinNode left root right height summary =>
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
        ((('index, 'node) avl_join_t1) -> 'summary) ->
        (('index, 'node) avl_join_t1) list -> 'summary)
      (measure : (('index, 'node) avl_join_t1) -> 'summary)
      (measure_closure :
        (('index, 'node) avl_join_t1) -> 'summary)
      (repr :
        (('index, 'carrier) avl_join_t2) ->
        ('index, 'node, 'summary) avl_join_model_tree)
      (m1 :
        (('index, 'carrier) avl_join_t2) ->
        ('index, 'node) avl_join_model)
      (o1 : ('carrier, 'index, 'node, 'summary) avl_join_view)
      (l : ('index, 'carrier) avl_join_t2)
      (r : ('index, 'carrier) avl_join_t2)
      (d : ('index, 'node) avl_join_t1).
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
         avl_join_balanced balancing agg measure_closure
           (repr self) /\
         avl_join_model_seq (m1 self) =
           avl_join_seq_model (repr self) /\
         avl_join_model_hgt (m1 self) =
           avl_join_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      view_ok balancing agg measure_closure
        (\x. avl_join_model_seq (m1 x))
        (\x. avl_join_model_hgt (m1 x))
        l o1
      ==>
      ((case o1 of
          AvlJoinEmpty => T
        | AvlJoinNode ll ld lr lh left_summary =>
            !o2 : ('carrier, 'index, 'node, 'summary) avl_join_view.
              view_ok balancing agg measure_closure
                (\x. avl_join_model_seq (m1 x))
                (\x. avl_join_model_hgt (m1 x))
                r o2
              ==>
              case o2 of
                AvlJoinEmpty => T
              | AvlJoinNode rl rd rr rh right_summary =>
                  !(negative_right_height : int).
                    negative_right_height = -(&rh)
                    ==>
                    (negative_right_height <= &lh - &rh /\
                     &lh - &rh <= &lh) /\
                    !(height_difference : int).
                      height_difference = &lh - &rh
                      ==>
                      if &balancing < height_difference then
                        (0 : int) <=
                          height_distance
                            (avl_join_model_hgt (m1 l))
                            (avl_join_model_hgt (m1 r)) /\
                        height_distance
                          (avl_join_model_hgt (m1 lr))
                          (avl_join_model_hgt (m1 r)) <
                        height_distance
                          (avl_join_model_hgt (m1 l))
                          (avl_join_model_hgt (m1 r)) /\
                        !right_child : ('index, 'carrier) avl_join_t2.
                          built_node
                            (\x. avl_join_model_seq (m1 x))
                            (\x. avl_join_model_hgt (m1 x))
                            right_child lr d r
                          ==>
                          -(&balancing) - 1 <=
                            avl_join_model_hgt (m1 ll) -
                            avl_join_model_hgt (m1 right_child) /\
                          avl_join_model_hgt (m1 ll) -
                            avl_join_model_hgt (m1 right_child) <=
                            &balancing + 1
                      else
                        !(negative_balancing : int).
                          negative_balancing = -(&balancing)
                          ==>
                          if height_difference < negative_balancing then
                            (0 : int) <=
                              height_distance
                                (avl_join_model_hgt (m1 l))
                                (avl_join_model_hgt (m1 r)) /\
                            height_distance
                              (avl_join_model_hgt (m1 l))
                              (avl_join_model_hgt (m1 rl)) <
                            height_distance
                              (avl_join_model_hgt (m1 l))
                              (avl_join_model_hgt (m1 r)) /\
                            !left_child :
                              ('index, 'carrier) avl_join_t2.
                              built_node
                                (\x. avl_join_model_seq (m1 x))
                                (\x. avl_join_model_hgt (m1 x))
                                left_child l d rl
                              ==>
                              -(&balancing) - 1 <=
                                avl_join_model_hgt (m1 left_child) -
                                avl_join_model_hgt (m1 rr) /\
                              avl_join_model_hgt (m1 left_child) -
                                avl_join_model_hgt (m1 rr) <=
                                &balancing + 1
                          else
                            within_balance balancing
                              (avl_join_model_hgt (m1 l))
                              (avl_join_model_hgt (m1 r))) /\
       !result : ('index, 'carrier) avl_join_t2.
         (case o1 of
            AvlJoinEmpty =>
              avl_join_model_seq (m1 result) =
                d :: avl_join_model_seq (m1 r) /\
              avl_join_model_hgt (m1 result) -
                avl_join_model_hgt (m1 r) <= 1 /\
              (0 : int) <=
                avl_join_model_hgt (m1 result) -
                avl_join_model_hgt (m1 r)
          | AvlJoinNode ll ld lr lh left_summary =>
              ?o2 : ('carrier, 'index, 'node, 'summary) avl_join_view.
                view_ok balancing agg measure_closure
                  (\x. avl_join_model_seq (m1 x))
                  (\x. avl_join_model_hgt (m1 x))
                  r o2 /\
                case o2 of
                  AvlJoinEmpty =>
                    avl_join_model_seq (m1 result) =
                      APPEND (avl_join_model_seq (m1 l)) [d] /\
                    avl_join_model_hgt (m1 result) -
                      avl_join_model_hgt (m1 l) <= 1 /\
                    (0 : int) <=
                      avl_join_model_hgt (m1 result) -
                      avl_join_model_hgt (m1 l)
                | AvlJoinNode rl rd rr rh right_summary =>
                    ?negative_right_height : int.
                      negative_right_height = -(&rh) /\
                      ?height_difference : int.
                        height_difference = &lh - &rh /\
                        if &balancing < height_difference then
                          ?right_child :
                            ('index, 'carrier) avl_join_t2.
                            built_node
                              (\x. avl_join_model_seq (m1 x))
                              (\x. avl_join_model_hgt (m1 x))
                              right_child lr d r /\
                            avl_join_model_seq (m1 result) =
                              node_model
                                (avl_join_model_seq (m1 ll))
                                ld
                                (avl_join_model_seq (m1 right_child)) /\
                            (let left_height =
                               avl_join_model_hgt (m1 ll)
                             in
                             let right_height =
                               avl_join_model_hgt (m1 right_child)
                             in
                             let expected =
                               expected_height
                                 left_height right_height
                             in
                             let result_height =
                               avl_join_model_hgt (m1 result)
                             in
                               one_step_height_loss
                                 expected result_height /\
                               (within_balance balancing
                                  left_height right_height
                                ==>
                                expected = result_height))
                        else
                          ?negative_balancing : int.
                            negative_balancing = -(&balancing) /\
                            if height_difference < negative_balancing then
                              ?left_child :
                                ('index, 'carrier) avl_join_t2.
                                built_node
                                  (\x. avl_join_model_seq (m1 x))
                                  (\x. avl_join_model_hgt (m1 x))
                                  left_child l d rl /\
                                avl_join_model_seq (m1 result) =
                                  node_model
                                    (avl_join_model_seq (m1 left_child))
                                    rd
                                    (avl_join_model_seq (m1 rr)) /\
                                (let left_height =
                                   avl_join_model_hgt (m1 left_child)
                                 in
                                 let right_height =
                                   avl_join_model_hgt (m1 rr)
                                 in
                                 let expected =
                                   expected_height
                                     left_height right_height
                                 in
                                 let result_height =
                                   avl_join_model_hgt (m1 result)
                                 in
                                   one_step_height_loss
                                     expected result_height /\
                                   (within_balance balancing
                                      left_height right_height
                                    ==>
                                    expected = result_height))
                            else
                              avl_join_model_seq (m1 result) =
                                node_model
                                  (avl_join_model_seq (m1 l))
                                  d
                                  (avl_join_model_seq (m1 r)) /\
                              avl_join_model_hgt (m1 result) =
                                expected_height
                                  (avl_join_model_hgt (m1 l))
                                  (avl_join_model_hgt (m1 r)))
         ==>
         avl_join_model_seq (m1 result) =
           node_model
             (avl_join_model_seq (m1 l))
             d
             (avl_join_model_seq (m1 r)) /\
         one_step_height_loss
           (expected_height
             (avl_join_model_hgt (m1 l))
             (avl_join_model_hgt (m1 r)))
           (avl_join_model_hgt (m1 result)))``;
