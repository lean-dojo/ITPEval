(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_decompose_front_nodeqtvc: an AVL-tree front-decomposition
  verification condition preserving sequence decomposition and height bounds
  across empty and node views. This file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus
  avl_decompose_t1 and avl_decompose_t2 are bijective indexed wrappers of
  their arbitrary underlying carriers, preserving the source t1 alpha and
  t2 alpha families without adding or removing data.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_decompose_t1 = AvlDecomposeT1 ('index -> unit) 'node
End

Datatype:
  avl_decompose_t2 = AvlDecomposeT2 ('index -> unit) 'carrier
End

Datatype:
  avl_decompose_model_tree =
    AvlDecomposeModelEmpty
  | AvlDecomposeModelNode avl_decompose_model_tree
      (('index, 'node) avl_decompose_t1)
      avl_decompose_model_tree num 'summary
End

Datatype:
  avl_decompose_model =
    AvlDecomposeModel ((('index, 'node) avl_decompose_t1) list) int
End

Datatype:
  avl_decompose_view =
    AvlDecomposeEmpty
  | AvlDecomposeNode
      (('carrier, 'index) avl_decompose_t2)
      (('index, 'node) avl_decompose_t1)
      (('carrier, 'index) avl_decompose_t2)
      num 'summary
End

val avl_decompose_model_seq_def = Define `
  avl_decompose_model_seq (AvlDecomposeModel elements height) = elements`;

val avl_decompose_model_hgt_def = Define `
  avl_decompose_model_hgt (AvlDecomposeModel elements height) = height`;

val avl_decompose_seq_model_def = Define `
  (avl_decompose_seq_model AvlDecomposeModelEmpty = []) /\
  (avl_decompose_seq_model
      (AvlDecomposeModelNode left root right height summary) =
     APPEND (avl_decompose_seq_model left)
       (root :: avl_decompose_seq_model right))`;

val avl_decompose_real_height_def = Define `
  (avl_decompose_real_height AvlDecomposeModelEmpty = (0 : int)) /\
  (avl_decompose_real_height
      (AvlDecomposeModelNode left root right height summary) =
     1 +
       (if avl_decompose_real_height left <
           avl_decompose_real_height right
        then avl_decompose_real_height right
        else avl_decompose_real_height left))`;

val avl_decompose_balanced_def = Define `
  (avl_decompose_balanced balancing agg measure_closure
      AvlDecomposeModelEmpty = T) /\
  (avl_decompose_balanced balancing agg measure_closure
      (AvlDecomposeModelNode left root right height summary) =
     (&height =
        avl_decompose_real_height
          (AvlDecomposeModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_decompose_seq_model
            (AvlDecomposeModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_decompose_real_height right -
        avl_decompose_real_height left /\
      avl_decompose_real_height right -
        avl_decompose_real_height left <= &balancing /\
      avl_decompose_balanced balancing agg measure_closure left /\
      avl_decompose_balanced balancing agg measure_closure right))`;

val avl_decompose_front_node_vc =
  ``let node_model =
      \left : (('index, 'node) avl_decompose_t1) list.
      \root : ('index, 'node) avl_decompose_t1.
      \right : (('index, 'node) avl_decompose_t1) list.
        APPEND left (root :: right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg :
        ((('index, 'node) avl_decompose_t1) -> 'summary) ->
        (('index, 'node) avl_decompose_t1) list -> 'summary)
      (measure : (('index, 'node) avl_decompose_t1) -> 'summary)
      (measure_closure :
        (('index, 'node) avl_decompose_t1) -> 'summary)
      (repr :
        (('carrier, 'index) avl_decompose_t2) ->
        ('index, 'node, 'summary) avl_decompose_model_tree)
      (m1 :
        (('carrier, 'index) avl_decompose_t2) ->
        ('index, 'node) avl_decompose_model)
      (l : ('carrier, 'index) avl_decompose_t2)
      (r : ('carrier, 'index) avl_decompose_t2)
      (o1 :
        ('carrier, 'index, 'node, 'summary) avl_decompose_view)
      (d : ('index, 'node) avl_decompose_t1).
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
         avl_decompose_balanced balancing agg measure_closure
           (repr self) /\
         avl_decompose_model_seq (m1 self) =
           avl_decompose_seq_model (repr self) /\
         avl_decompose_model_hgt (m1 self) =
           avl_decompose_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      -(&balancing) <=
        avl_decompose_model_hgt (m1 l) -
        avl_decompose_model_hgt (m1 r) ==>
      avl_decompose_model_hgt (m1 l) -
        avl_decompose_model_hgt (m1 r) <= &balancing ==>
      (case o1 of
         AvlDecomposeEmpty =>
           avl_decompose_model_hgt (m1 l) = 0 /\
           avl_decompose_model_seq (m1 l) = []
       | AvlDecomposeNode l1 root r1 height summary =>
           avl_decompose_model_seq (m1 l) =
             node_model
               (avl_decompose_model_seq (m1 l1))
               root
               (avl_decompose_model_seq (m1 r1)) /\
           summary =
             agg measure_closure
               (avl_decompose_model_seq (m1 l)) /\
           -(&balancing) <=
             avl_decompose_model_hgt (m1 l1) -
             avl_decompose_model_hgt (m1 r1) /\
           avl_decompose_model_hgt (m1 l1) -
             avl_decompose_model_hgt (m1 r1) <= &balancing /\
           avl_decompose_model_hgt (m1 l) = &height /\
           &height =
             1 +
             (if avl_decompose_model_hgt (m1 l1) <
                 avl_decompose_model_hgt (m1 r1)
              then avl_decompose_model_hgt (m1 r1)
              else avl_decompose_model_hgt (m1 l1)))
      ==>
      ((case o1 of
          AvlDecomposeEmpty => T
        | AvlDecomposeNode l1 d2 r2 height summary =>
            (((0 : int) <= avl_decompose_model_hgt (m1 l) /\
              avl_decompose_model_hgt (m1 l1) <
                avl_decompose_model_hgt (m1 l)) /\
             -(&balancing) <=
               avl_decompose_model_hgt (m1 l1) -
               avl_decompose_model_hgt (m1 r2) /\
             avl_decompose_model_hgt (m1 l1) -
               avl_decompose_model_hgt (m1 r2) <= &balancing) /\
            !d3 : ('index, 'node) avl_decompose_t1.
            !left1 : ('carrier, 'index) avl_decompose_t2.
              (node_model
                 (avl_decompose_model_seq (m1 l1))
                 d2
                 (avl_decompose_model_seq (m1 r2)) =
                 d3 :: avl_decompose_model_seq (m1 left1) /\
               (let hl = avl_decompose_model_hgt (m1 l1) in
                let hr = avl_decompose_model_hgt (m1 r2) in
                let he = 1 + (if hl < hr then hr else hl)
                in
                  (0 : int) <=
                    he - avl_decompose_model_hgt (m1 left1) /\
                  he - avl_decompose_model_hgt (m1 left1) <= 1))
              ==>
              -(&balancing) - 1 <=
                avl_decompose_model_hgt (m1 left1) -
                avl_decompose_model_hgt (m1 r) /\
              avl_decompose_model_hgt (m1 left1) -
                avl_decompose_model_hgt (m1 r) <=
                &balancing + 1) /\
       !d2 : ('index, 'node) avl_decompose_t1.
       !res : ('carrier, 'index) avl_decompose_t2.
         (case o1 of
            AvlDecomposeEmpty =>
              d2 = d /\ res = r
          | AvlDecomposeNode l1 d21 r2 height summary =>
              ?res1 : ('carrier, 'index) avl_decompose_t2.
                (node_model
                   (avl_decompose_model_seq (m1 l1))
                   d21
                   (avl_decompose_model_seq (m1 r2)) =
                   d2 :: avl_decompose_model_seq (m1 res1) /\
                 (let hl = avl_decompose_model_hgt (m1 l1) in
                  let hr = avl_decompose_model_hgt (m1 r2) in
                  let he = 1 + (if hl < hr then hr else hl)
                  in
                    (0 : int) <=
                      he - avl_decompose_model_hgt (m1 res1) /\
                    he - avl_decompose_model_hgt (m1 res1) <= 1)) /\
                avl_decompose_model_seq (m1 res) =
                  node_model
                    (avl_decompose_model_seq (m1 res1))
                    d
                    (avl_decompose_model_seq (m1 r)) /\
                (let hl = avl_decompose_model_hgt (m1 res1) in
                 let hr = avl_decompose_model_hgt (m1 r) in
                 let he = 1 + (if hl < hr then hr else hl) in
                 let hres = avl_decompose_model_hgt (m1 res)
                 in
                   ((0 : int) <= he - hres /\
                    he - hres <= 1) /\
                   ((-(&balancing) <= hl - hr /\
                     hl - hr <= &balancing)
                    ==>
                    he = hres)))
         ==>
         node_model
           (avl_decompose_model_seq (m1 l))
           d
           (avl_decompose_model_seq (m1 r)) =
           d2 :: avl_decompose_model_seq (m1 res) /\
         (let hl = avl_decompose_model_hgt (m1 l) in
          let hr = avl_decompose_model_hgt (m1 r) in
          let he = 1 + (if hl < hr then hr else hl)
          in
            (0 : int) <= he - avl_decompose_model_hgt (m1 res) /\
            he - avl_decompose_model_hgt (m1 res) <= 1))``;
