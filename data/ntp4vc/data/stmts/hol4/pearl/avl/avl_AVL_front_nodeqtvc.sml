(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_front_nodeqtvc: an AVL-tree front-node verification
  condition relating a node view's sequence and height data to the returned
  initial sequence element and strict height growth. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_front_model_tree =
    AvlFrontModelEmpty
  | AvlFrontModelNode avl_front_model_tree 'node
      avl_front_model_tree num 'summary
End

Datatype:
  avl_front_model = AvlFrontModel ('node list) int
End

Datatype:
  avl_front_view =
    AvlFrontEmpty
  | AvlFrontNode 'carrier 'node 'carrier num 'summary
End

val avl_front_model_seq_def = Define `
  avl_front_model_seq (AvlFrontModel elements height) = elements`;

val avl_front_model_hgt_def = Define `
  avl_front_model_hgt (AvlFrontModel elements height) = height`;

val avl_front_seq_model_def = Define `
  (avl_front_seq_model AvlFrontModelEmpty = []) /\
  (avl_front_seq_model
      (AvlFrontModelNode left root right height summary) =
     APPEND (avl_front_seq_model left)
       (root :: avl_front_seq_model right))`;

val avl_front_real_height_def = Define `
  (avl_front_real_height AvlFrontModelEmpty = (0 : int)) /\
  (avl_front_real_height
      (AvlFrontModelNode left root right height summary) =
     1 +
       (if avl_front_real_height left < avl_front_real_height right
        then avl_front_real_height right
        else avl_front_real_height left))`;

val avl_front_balanced_def = Define `
  (avl_front_balanced balancing agg measure_closure
      AvlFrontModelEmpty = T) /\
  (avl_front_balanced balancing agg measure_closure
      (AvlFrontModelNode left root right height summary) =
     (&height =
        avl_front_real_height
          (AvlFrontModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_front_seq_model
            (AvlFrontModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_front_real_height right -
        avl_front_real_height left /\
      avl_front_real_height right -
        avl_front_real_height left <= &balancing /\
      avl_front_balanced balancing agg measure_closure left /\
      avl_front_balanced balancing agg measure_closure right))`;

val avl_front_node_vc =
  ``let node_model =
      \left : 'node list. \root : 'node. \right : 'node list.
        APPEND left (root :: right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg : ('node -> 'summary) -> 'node list -> 'summary)
      (measure : 'node -> 'summary)
      (measure_closure : 'node -> 'summary)
      (repr :
        'carrier -> ('node, 'summary) avl_front_model_tree)
      (m1 : 'carrier -> 'node avl_front_model)
      (o1 : ('carrier, 'node, 'summary) avl_front_view)
      (l : 'carrier)
      (d : 'node).
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
         avl_front_balanced balancing agg measure_closure
           (repr self) /\
         avl_front_model_seq (m1 self) =
           avl_front_seq_model (repr self) /\
         avl_front_model_hgt (m1 self) =
           avl_front_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      (case o1 of
         AvlFrontEmpty =>
           avl_front_model_hgt (m1 l) = 0 /\
           avl_front_model_seq (m1 l) = []
       | AvlFrontNode l1 d2 r h s =>
           avl_front_model_seq (m1 l) =
             node_model
               (avl_front_model_seq (m1 l1))
               d2
               (avl_front_model_seq (m1 r)) /\
           s =
             agg measure_closure
               (avl_front_model_seq (m1 l)) /\
           -(&balancing) <=
             avl_front_model_hgt (m1 l1) -
             avl_front_model_hgt (m1 r) /\
           avl_front_model_hgt (m1 l1) -
             avl_front_model_hgt (m1 r) <= &balancing /\
           avl_front_model_hgt (m1 l) = &h /\
           &h =
             1 +
             (if avl_front_model_hgt (m1 l1) <
                 avl_front_model_hgt (m1 r)
              then avl_front_model_hgt (m1 r)
              else avl_front_model_hgt (m1 l1)))
      ==>
      ((case o1 of
          AvlFrontEmpty => T
        | AvlFrontNode l1 d2 r h s =>
            (0 : int) <= avl_front_model_hgt (m1 l) /\
            avl_front_model_hgt (m1 l1) <
              avl_front_model_hgt (m1 l)) /\
       !result : 'node.
         (case o1 of
            AvlFrontEmpty => result = d
          | AvlFrontNode l1 d2 r h s =>
              result =
                EL 0
                  (APPEND
                    (avl_front_model_seq (m1 l1))
                    [d2]))
         ==>
         result =
           EL 0
             (APPEND
               (avl_front_model_seq (m1 l))
               [d]))``;
