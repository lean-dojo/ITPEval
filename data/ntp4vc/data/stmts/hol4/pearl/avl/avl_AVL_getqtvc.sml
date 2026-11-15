(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_getqtvc: an AVL-tree selector verification condition
  preserving sequence splits and optional selected elements across empty,
  left-subtree, right-subtree, and root-selection cases. This file contains
  no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus avl_get_t1
  and avl_get_t2 are bijective indexed wrappers of their arbitrary underlying
  carriers, preserving the source t1 alpha and t2 alpha families without
  adding or removing data.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_get_t1 = AvlGetT1 ('index -> unit) 'node
End

Datatype:
  avl_get_t2 = AvlGetT2 ('index -> unit) 'carrier
End

Datatype:
  avl_get_model_tree =
    AvlGetModelEmpty
  | AvlGetModelNode avl_get_model_tree
      (('index, 'node) avl_get_t1)
      avl_get_model_tree num 'summary
End

Datatype:
  avl_get_model =
    AvlGetModel ((('index, 'node) avl_get_t1) list) int
End

Datatype:
  avl_get_view =
    AvlGetEmpty
  | AvlGetNode
      (('carrier, 'index) avl_get_t2)
      (('index, 'node) avl_get_t1)
      (('carrier, 'index) avl_get_t2)
      num 'summary
End

Datatype:
  avl_get_split = AvlGetSplit ('a list) ('a option) ('a list)
End

Datatype:
  avl_get_part_base =
    AvlGetLeft 'selector
  | AvlGetRight 'selector
  | AvlGetHere
End

val avl_get_model_seq_def = Define `
  avl_get_model_seq (AvlGetModel elements height) = elements`;

val avl_get_model_hgt_def = Define `
  avl_get_model_hgt (AvlGetModel elements height) = height`;

val avl_get_split_left_def = Define `
  avl_get_split_left (AvlGetSplit left middle right) = left`;

val avl_get_split_middle_def = Define `
  avl_get_split_middle (AvlGetSplit left middle right) = middle`;

val avl_get_split_right_def = Define `
  avl_get_split_right (AvlGetSplit left middle right) = right`;

val avl_get_option_to_seq_def = Define `
  (avl_get_option_to_seq NONE = []) /\
  (avl_get_option_to_seq (SOME element) = [element])`;

val avl_get_rebuild_def = Define `
  avl_get_rebuild split =
    APPEND
      (APPEND
        (avl_get_split_left split)
        (avl_get_option_to_seq (avl_get_split_middle split)))
      (avl_get_split_right split)`;

val avl_get_left_extend_def = Define `
  avl_get_left_extend left root split =
    AvlGetSplit
      (APPEND left (root :: avl_get_split_left split))
      (avl_get_split_middle split)
      (avl_get_split_right split)`;

val avl_get_right_extend_def = Define `
  avl_get_right_extend split root right =
    AvlGetSplit
      (avl_get_split_left split)
      (avl_get_split_middle split)
      (APPEND (avl_get_split_right split) (root :: right))`;

val avl_get_seq_model_def = Define `
  (avl_get_seq_model AvlGetModelEmpty = []) /\
  (avl_get_seq_model
      (AvlGetModelNode left root right height summary) =
     APPEND (avl_get_seq_model left)
       (root :: avl_get_seq_model right))`;

val avl_get_real_height_def = Define `
  (avl_get_real_height AvlGetModelEmpty = (0 : int)) /\
  (avl_get_real_height
      (AvlGetModelNode left root right height summary) =
     1 +
       (if avl_get_real_height left < avl_get_real_height right
        then avl_get_real_height right
        else avl_get_real_height left))`;

val avl_get_balanced_def = Define `
  (avl_get_balanced balancing agg measure_closure
      AvlGetModelEmpty = T) /\
  (avl_get_balanced balancing agg measure_closure
      (AvlGetModelNode left root right height summary) =
     (&height =
        avl_get_real_height
          (AvlGetModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_get_seq_model
            (AvlGetModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_get_real_height right -
        avl_get_real_height left /\
      avl_get_real_height right -
        avl_get_real_height left <= &balancing /\
      avl_get_balanced balancing agg measure_closure left /\
      avl_get_balanced balancing agg measure_closure right))`;

val avl_get_vc =
  ``let node_model =
      \left : (('index, 'node) avl_get_t1) list.
      \root : ('index, 'node) avl_get_t1.
      \right : (('index, 'node) avl_get_t1) list.
        APPEND left (root :: right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg :
        ((('index, 'node) avl_get_t1) -> 'summary) ->
        (('index, 'node) avl_get_t1) list -> 'summary)
      (measure : (('index, 'node) avl_get_t1) -> 'summary)
      (measure_closure :
        (('index, 'node) avl_get_t1) -> 'summary)
      (repr :
        (('carrier, 'index) avl_get_t2) ->
        ('index, 'node, 'summary) avl_get_model_tree)
      (m1 :
        (('carrier, 'index) avl_get_t2) ->
        ('index, 'node) avl_get_model)
      (selected :
        'selector ->
        ((('index, 'node) avl_get_t1) avl_get_split) -> bool)
      (selection_possible :
        'selector ->
        (('index, 'node) avl_get_t1) list -> bool)
      (s : 'selector)
      (t3 : ('carrier, 'index) avl_get_t2)
      (o1 :
        ('carrier, 'index, 'node, 'summary) avl_get_view).
      (0 : int) < &balancing ==>
      (!a b c. op a (op b c) = op (op a b) c) ==>
      (!x. op x zero = x /\ x = op zero x) ==>
      (!f. agg f [] = zero) ==>
      (!elements f.
         LENGTH elements = 1 ==>
         agg f elements = f (EL 0 elements)) ==>
      (!f left right.
         agg f (APPEND left right) =
         op (agg f left) (agg f right)) ==>
      (!element. measure_closure element = measure element) ==>
      (!self.
         avl_get_balanced balancing agg measure_closure
           (repr self) /\
         avl_get_model_seq (m1 self) =
           avl_get_seq_model (repr self) /\
         avl_get_model_hgt (m1 self) =
           avl_get_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      (!selector.
         selection_possible selector [] ==>
         selected selector (AvlGetSplit [] NONE [])) ==>
      selection_possible s (avl_get_model_seq (m1 t3)) ==>
      (case o1 of
         AvlGetEmpty =>
           avl_get_model_hgt (m1 t3) = 0 /\
           avl_get_model_seq (m1 t3) = []
       | AvlGetNode left root right height summary =>
           avl_get_model_seq (m1 t3) =
             node_model
               (avl_get_model_seq (m1 left))
               root
               (avl_get_model_seq (m1 right)) /\
           summary =
             agg measure_closure
               (avl_get_model_seq (m1 t3)) /\
           -(&balancing) <=
             avl_get_model_hgt (m1 left) -
             avl_get_model_hgt (m1 right) /\
           avl_get_model_hgt (m1 left) -
             avl_get_model_hgt (m1 right) <= &balancing /\
           avl_get_model_hgt (m1 t3) = &height /\
           &height =
             1 +
             (if avl_get_model_hgt (m1 left) <
                 avl_get_model_hgt (m1 right)
              then avl_get_model_hgt (m1 right)
              else avl_get_model_hgt (m1 left)))
      ==>
      (case o1 of
         AvlGetEmpty =>
           let empty_split =
             (AvlGetSplit [] NONE [] :
               ((('index, 'node) avl_get_t1) avl_get_split))
           in
             (selected s empty_split /\
              avl_get_rebuild empty_split =
                avl_get_model_seq (m1 t3)) /\
             avl_get_split_middle empty_split = NONE
       | AvlGetNode tree_left tree_root tree_right height summary =>
           let right_seq = avl_get_model_seq (m1 tree_right) in
           let left_seq = avl_get_model_seq (m1 tree_left)
           in
             (selection_possible s
                (node_model left_seq tree_root right_seq) /\
              agg measure_closure
                (avl_get_model_seq (m1 tree_left)) =
                agg measure_closure left_seq /\
              agg measure_closure
                (avl_get_model_seq (m1 tree_right)) =
                agg measure_closure right_seq) /\
             !(part : 'selector avl_get_part_base).
               (case part of
                  AvlGetHere =>
                    selected s
                      (AvlGetSplit left_seq
                        (SOME tree_root) right_seq)
                | AvlGetLeft left_selector =>
                    selection_possible left_selector left_seq /\
                    !split.
                      (selected left_selector split /\
                       avl_get_rebuild split = left_seq)
                      ==>
                      selected s
                        (avl_get_right_extend
                          split tree_root right_seq)
                | AvlGetRight right_selector =>
                    selection_possible right_selector right_seq /\
                    !split.
                      (selected right_selector split /\
                       avl_get_rebuild split = right_seq)
                      ==>
                      selected s
                        (avl_get_left_extend
                          left_seq tree_root split))
               ==>
               (case part of
                  AvlGetLeft left_selector =>
                    (((0 : int) <=
                        avl_get_model_hgt (m1 t3) /\
                      avl_get_model_hgt (m1 tree_left) <
                        avl_get_model_hgt (m1 t3)) /\
                     selection_possible left_selector
                       (avl_get_model_seq (m1 tree_left))) /\
                    !split
                      (result :
                        (('index, 'node) avl_get_t1) option).
                      ((selected left_selector split /\
                        avl_get_rebuild split =
                          avl_get_model_seq (m1 tree_left)) /\
                       (case result of
                          NONE =>
                            avl_get_split_middle split = NONE
                        | SOME element =>
                            avl_get_split_middle split =
                              SOME element))
                      ==>
                      (selected s
                         (avl_get_right_extend
                           split tree_root
                           (avl_get_model_seq (m1 tree_right))) /\
                       avl_get_rebuild
                         (avl_get_right_extend
                           split tree_root
                           (avl_get_model_seq (m1 tree_right))) =
                         avl_get_model_seq (m1 t3)) /\
                      (case result of
                         NONE =>
                           avl_get_split_middle
                             (avl_get_right_extend
                               split tree_root
                               (avl_get_model_seq (m1 tree_right))) =
                             NONE
                       | SOME element =>
                           avl_get_split_middle
                             (avl_get_right_extend
                               split tree_root
                               (avl_get_model_seq (m1 tree_right))) =
                             SOME element)
                | AvlGetRight right_selector =>
                    (((0 : int) <=
                        avl_get_model_hgt (m1 t3) /\
                      avl_get_model_hgt (m1 tree_right) <
                        avl_get_model_hgt (m1 t3)) /\
                     selection_possible right_selector
                       (avl_get_model_seq (m1 tree_right))) /\
                    !split
                      (result :
                        (('index, 'node) avl_get_t1) option).
                      ((selected right_selector split /\
                        avl_get_rebuild split =
                          avl_get_model_seq (m1 tree_right)) /\
                       (case result of
                          NONE =>
                            avl_get_split_middle split = NONE
                        | SOME element =>
                            avl_get_split_middle split =
                              SOME element))
                      ==>
                      (selected s
                         (avl_get_left_extend
                           (avl_get_model_seq (m1 tree_left))
                           tree_root split) /\
                       avl_get_rebuild
                         (avl_get_left_extend
                           (avl_get_model_seq (m1 tree_left))
                           tree_root split) =
                         avl_get_model_seq (m1 t3)) /\
                      (case result of
                         NONE =>
                           avl_get_split_middle
                             (avl_get_left_extend
                               (avl_get_model_seq (m1 tree_left))
                               tree_root split) =
                             NONE
                       | SOME element =>
                           avl_get_split_middle
                             (avl_get_left_extend
                               (avl_get_model_seq (m1 tree_left))
                               tree_root split) =
                             SOME element)
                | AvlGetHere =>
                    (selected s
                       (AvlGetSplit
                         (avl_get_model_seq (m1 tree_left))
                         (SOME tree_root)
                         (avl_get_model_seq (m1 tree_right))) /\
                     avl_get_rebuild
                       (AvlGetSplit
                         (avl_get_model_seq (m1 tree_left))
                         (SOME tree_root)
                         (avl_get_model_seq (m1 tree_right))) =
                       avl_get_model_seq (m1 t3)) /\
                    avl_get_split_middle
                      (AvlGetSplit
                        (avl_get_model_seq (m1 tree_left))
                        (SOME tree_root)
                        (avl_get_model_seq (m1 tree_right))) =
                      SOME tree_root))``;
