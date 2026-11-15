(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_snocqtvc: an AVL-tree right-insertion (snoc)
  verification condition with the source aggregation laws, positive balance
  bound, indexed node and tree carriers, and recursive representation
  invariants. This file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus avl_t1 and
  avl_t2 are bijective indexed wrappers of their arbitrary underlying
  carriers, preserving the t1 alpha and t2 alpha families without adding or
  removing data.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_t1 = AvlT1 ('index -> unit) 'node
End

Datatype:
  avl_t2 = AvlT2 ('index -> unit) 'carrier
End

Datatype:
  avl_model_tree =
    AvlModelEmpty
  | AvlModelNode avl_model_tree
      (('index, 'node) avl_t1)
      avl_model_tree num 'summary
End

Datatype:
  avl_model = AvlModel ((('index, 'node) avl_t1) list) int
End

Datatype:
  avl_snoc_view =
    AvlSnocEmpty
  | AvlSnocNode
      (('index, 'carrier) avl_t2)
      (('index, 'node) avl_t1)
      (('index, 'carrier) avl_t2)
      num 'summary
End

val avl_model_seq_def = Define `
  avl_model_seq (AvlModel elements height) = elements`;

val avl_model_hgt_def = Define `
  avl_model_hgt (AvlModel elements height) = height`;

val avl_seq_model_def = Define `
  (avl_seq_model AvlModelEmpty = []) /\
  (avl_seq_model (AvlModelNode left root right height summary) =
     APPEND (avl_seq_model left) (root :: avl_seq_model right))`;

val avl_real_height_def = Define `
  (avl_real_height AvlModelEmpty = (0 : int)) /\
  (avl_real_height (AvlModelNode left root right height summary) =
     1 + (if avl_real_height left < avl_real_height right
          then avl_real_height right
          else avl_real_height left))`;

val avl_balanced_def = Define `
  (avl_balanced balancing agg measure_closure AvlModelEmpty = T) /\
  (avl_balanced balancing agg measure_closure
      (AvlModelNode left root right height summary) =
     (&height =
        avl_real_height
          (AvlModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_seq_model
            (AvlModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_real_height right - avl_real_height left /\
      avl_real_height right - avl_real_height left <= &balancing /\
      avl_balanced balancing agg measure_closure left /\
      avl_balanced balancing agg measure_closure right))`;

val avl_snoc_vc =
  ``let node_model =
      \left : (('index, 'node) avl_t1) list.
      \root : ('index, 'node) avl_t1.
      \right : (('index, 'node) avl_t1) list.
        APPEND left (root :: right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg :
        ((('index, 'node) avl_t1) -> 'summary) ->
        (('index, 'node) avl_t1) list -> 'summary)
      (measure : (('index, 'node) avl_t1) -> 'summary)
      (measure_closure : (('index, 'node) avl_t1) -> 'summary)
      (repr :
        (('index, 'carrier) avl_t2) ->
        ('index, 'node, 'summary) avl_model_tree)
      (m1 :
        (('index, 'carrier) avl_t2) ->
        ('index, 'node) avl_model)
      (o1 :
        ('index, 'carrier, 'node, 'summary) avl_snoc_view)
      (t3 : ('index, 'carrier) avl_t2)
      (d : ('index, 'node) avl_t1).
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
         avl_balanced balancing agg measure_closure (repr self) /\
         avl_model_seq (m1 self) = avl_seq_model (repr self) /\
         avl_model_hgt (m1 self) = avl_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      (case o1 of
         AvlSnocEmpty =>
           avl_model_hgt (m1 t3) = 0 /\
           avl_model_seq (m1 t3) = []
       | AvlSnocNode l d2 r h s =>
           avl_model_seq (m1 t3) =
             node_model
               (avl_model_seq (m1 l))
               d2
               (avl_model_seq (m1 r)) /\
           s =
             agg measure_closure
               (avl_model_seq (m1 t3)) /\
           -(&balancing) <=
             avl_model_hgt (m1 l) -
             avl_model_hgt (m1 r) /\
           avl_model_hgt (m1 l) -
             avl_model_hgt (m1 r) <= &balancing /\
           avl_model_hgt (m1 t3) = &h /\
           &h =
             1 +
             (if avl_model_hgt (m1 l) <
                 avl_model_hgt (m1 r)
              then avl_model_hgt (m1 r)
              else avl_model_hgt (m1 l)))
      ==>
      ((case o1 of
          AvlSnocEmpty => T
        | AvlSnocNode l d2 r h s =>
            (0 <= avl_model_hgt (m1 t3) /\
             avl_model_hgt (m1 r) <
               avl_model_hgt (m1 t3)) /\
            !o2 : ('index, 'carrier) avl_t2.
              (avl_model_seq (m1 o2) =
                 APPEND (avl_model_seq (m1 r)) [d] /\
               avl_model_hgt (m1 o2) -
                 avl_model_hgt (m1 r) <= 1 /\
               0 <=
                 avl_model_hgt (m1 o2) -
                 avl_model_hgt (m1 r))
              ==>
              -(&balancing) - 1 <=
                avl_model_hgt (m1 l) -
                avl_model_hgt (m1 o2) /\
              avl_model_hgt (m1 l) -
                avl_model_hgt (m1 o2) <=
                &balancing + 1) /\
       !result : ('index, 'carrier) avl_t2.
         (case o1 of
            AvlSnocEmpty =>
              avl_model_seq (m1 result) = [d] /\
              avl_model_hgt (m1 result) = 1
          | AvlSnocNode l d2 r h s =>
              ?o2 : ('index, 'carrier) avl_t2.
                (avl_model_seq (m1 o2) =
                   APPEND (avl_model_seq (m1 r)) [d] /\
                 avl_model_hgt (m1 o2) -
                   avl_model_hgt (m1 r) <= 1 /\
                 0 <=
                   avl_model_hgt (m1 o2) -
                   avl_model_hgt (m1 r)) /\
                avl_model_seq (m1 result) =
                  node_model
                    (avl_model_seq (m1 l))
                    d2
                    (avl_model_seq (m1 o2)) /\
                (let hl = avl_model_hgt (m1 l) in
                 let hr = avl_model_hgt (m1 o2) in
                 let he =
                   1 + (if hl < hr then hr else hl)
                 in
                 let hres = avl_model_hgt (m1 result) in
                   (0 <= he - hres /\
                    he - hres <= 1) /\
                   ((-(&balancing) <= hl - hr /\
                     hl - hr <= &balancing)
                    ==>
                    he = hres)))
         ==>
         avl_model_seq (m1 result) =
           APPEND (avl_model_seq (m1 t3)) [d] /\
         avl_model_hgt (m1 result) -
           avl_model_hgt (m1 t3) <= 1 /\
         0 <=
           avl_model_hgt (m1 result) -
           avl_model_hgt (m1 t3))``;
