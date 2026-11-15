(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_back_nodeqtvc: an AVL-tree back-node verification
  condition relating a node view's sequence and height data to the returned
  final sequence element and strict height growth. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_back_model_tree =
    AvlBackModelEmpty
  | AvlBackModelNode avl_back_model_tree 'node
      avl_back_model_tree num 'summary
End

Datatype:
  avl_back_model = AvlBackModel ('node list) int
End

Datatype:
  avl_back_view =
    AvlBackEmpty
  | AvlBackNode 'carrier 'node 'carrier num 'summary
End

val avl_back_model_seq_def = Define `
  avl_back_model_seq (AvlBackModel elements height) = elements`;

val avl_back_model_hgt_def = Define `
  avl_back_model_hgt (AvlBackModel elements height) = height`;

val avl_back_seq_model_def = Define `
  (avl_back_seq_model AvlBackModelEmpty = []) /\
  (avl_back_seq_model
      (AvlBackModelNode left root right height summary) =
     APPEND (avl_back_seq_model left)
       (root :: avl_back_seq_model right))`;

val avl_back_real_height_def = Define `
  (avl_back_real_height AvlBackModelEmpty = (0 : int)) /\
  (avl_back_real_height
      (AvlBackModelNode left root right height summary) =
     1 +
       (if avl_back_real_height left < avl_back_real_height right
        then avl_back_real_height right
        else avl_back_real_height left))`;

val avl_back_balanced_def = Define `
  (avl_back_balanced balancing agg measure_closure
      AvlBackModelEmpty = T) /\
  (avl_back_balanced balancing agg measure_closure
      (AvlBackModelNode left root right height summary) =
     (&height =
        avl_back_real_height
          (AvlBackModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_back_seq_model
            (AvlBackModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_back_real_height right -
        avl_back_real_height left /\
      avl_back_real_height right -
        avl_back_real_height left <= &balancing /\
      avl_back_balanced balancing agg measure_closure left /\
      avl_back_balanced balancing agg measure_closure right))`;

val avl_back_node_vc =
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
        'carrier -> ('node, 'summary) avl_back_model_tree)
      (m1 : 'carrier -> 'node avl_back_model)
      (o1 : ('carrier, 'node, 'summary) avl_back_view)
      (r : 'carrier)
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
         avl_back_balanced balancing agg measure_closure
           (repr self) /\
         avl_back_model_seq (m1 self) =
           avl_back_seq_model (repr self) /\
         avl_back_model_hgt (m1 self) =
           avl_back_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      (case o1 of
         AvlBackEmpty =>
           avl_back_model_hgt (m1 r) = 0 /\
           avl_back_model_seq (m1 r) = []
       | AvlBackNode l d2 r1 h s =>
           avl_back_model_seq (m1 r) =
             node_model
               (avl_back_model_seq (m1 l))
               d2
               (avl_back_model_seq (m1 r1)) /\
           s =
             agg measure_closure
               (avl_back_model_seq (m1 r)) /\
           -(&balancing) <=
             avl_back_model_hgt (m1 l) -
             avl_back_model_hgt (m1 r1) /\
           avl_back_model_hgt (m1 l) -
             avl_back_model_hgt (m1 r1) <= &balancing /\
           avl_back_model_hgt (m1 r) = &h /\
           &h =
             1 +
             (if avl_back_model_hgt (m1 l) <
                 avl_back_model_hgt (m1 r1)
              then avl_back_model_hgt (m1 r1)
              else avl_back_model_hgt (m1 l)))
      ==>
      ((case o1 of
          AvlBackEmpty => T
        | AvlBackNode l d2 r1 h s =>
            (0 : int) <= avl_back_model_hgt (m1 r) /\
            avl_back_model_hgt (m1 r1) <
              avl_back_model_hgt (m1 r)) /\
       !result : 'node.
         (case o1 of
            AvlBackEmpty => result = d
          | AvlBackNode l d2 r1 h s =>
              result =
                EL
                  (LENGTH (avl_back_model_seq (m1 r1)))
                  (d2 :: avl_back_model_seq (m1 r1)))
         ==>
         result =
           EL
             (LENGTH (avl_back_model_seq (m1 r)))
             (d :: avl_back_model_seq (m1 r)))``;
