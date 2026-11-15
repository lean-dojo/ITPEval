(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_splitqtvc: an AVL-tree split verification condition
  preserving rebuilt sequences and the left, middle, and right components
  across empty, left-subtree, right-subtree, and root-selection cases. This
  file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus avl_split_t1
  and avl_split_t2 are bijective indexed wrappers of their arbitrary
  underlying carriers, preserving the source t1 alpha and t2 alpha families
  without adding or removing data.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_split_t1 = AvlSplitT1 ('index -> unit) 'node
End

Datatype:
  avl_split_t2 = AvlSplitT2 ('index -> unit) 'carrier
End

Datatype:
  avl_split_model_tree =
    AvlSplitModelEmpty
  | AvlSplitModelNode avl_split_model_tree
      (('index, 'node) avl_split_t1)
      avl_split_model_tree num 'summary
End

Datatype:
  avl_split_model =
    AvlSplitModel ((('index, 'node) avl_split_t1) list) int
End

Datatype:
  avl_split_view =
    AvlSplitEmpty
  | AvlSplitNode
      (('carrier, 'index) avl_split_t2)
      (('index, 'node) avl_split_t1)
      (('carrier, 'index) avl_split_t2)
      num 'summary
End

Datatype:
  avl_split_split = AvlSplitSplit ('a list) ('a option) ('a list)
End

Datatype:
  avl_split_part_base =
    AvlSplitLeft 'selector
  | AvlSplitRight 'selector
  | AvlSplitHere
End

val avl_split_model_seq_def = Define `
  avl_split_model_seq (AvlSplitModel elements height) = elements`;

val avl_split_model_hgt_def = Define `
  avl_split_model_hgt (AvlSplitModel elements height) = height`;

val avl_split_split_left_def = Define `
  avl_split_split_left (AvlSplitSplit left middle right) = left`;

val avl_split_split_middle_def = Define `
  avl_split_split_middle (AvlSplitSplit left middle right) = middle`;

val avl_split_split_right_def = Define `
  avl_split_split_right (AvlSplitSplit left middle right) = right`;

val avl_split_option_to_seq_def = Define `
  (avl_split_option_to_seq NONE = []) /\
  (avl_split_option_to_seq (SOME element) = [element])`;

val avl_split_rebuild_def = Define `
  avl_split_rebuild split =
    APPEND
      (APPEND
        (avl_split_split_left split)
        (avl_split_option_to_seq (avl_split_split_middle split)))
      (avl_split_split_right split)`;

val avl_split_left_extend_def = Define `
  avl_split_left_extend left root split =
    AvlSplitSplit
      (APPEND left (root :: avl_split_split_left split))
      (avl_split_split_middle split)
      (avl_split_split_right split)`;

val avl_split_right_extend_def = Define `
  avl_split_right_extend split root right =
    AvlSplitSplit
      (avl_split_split_left split)
      (avl_split_split_middle split)
      (APPEND (avl_split_split_right split) (root :: right))`;

val avl_split_seq_model_def = Define `
  (avl_split_seq_model AvlSplitModelEmpty = []) /\
  (avl_split_seq_model
      (AvlSplitModelNode left root right height summary) =
     APPEND (avl_split_seq_model left)
       (root :: avl_split_seq_model right))`;

val avl_split_real_height_def = Define `
  (avl_split_real_height AvlSplitModelEmpty = (0 : int)) /\
  (avl_split_real_height
      (AvlSplitModelNode left root right height summary) =
     1 +
       (if avl_split_real_height left < avl_split_real_height right
        then avl_split_real_height right
        else avl_split_real_height left))`;

val avl_split_balanced_def = Define `
  (avl_split_balanced balancing agg measure_closure
      AvlSplitModelEmpty = T) /\
  (avl_split_balanced balancing agg measure_closure
      (AvlSplitModelNode left root right height summary) =
     (&height =
        avl_split_real_height
          (AvlSplitModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_split_seq_model
            (AvlSplitModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_split_real_height right -
        avl_split_real_height left /\
      avl_split_real_height right -
        avl_split_real_height left <= &balancing /\
      avl_split_balanced balancing agg measure_closure left /\
      avl_split_balanced balancing agg measure_closure right))`;

val avl_split_vc =
  ``let node_model =
      \left : (('index, 'node) avl_split_t1) list.
      \root : ('index, 'node) avl_split_t1.
      \right : (('index, 'node) avl_split_t1) list.
        APPEND left (root :: right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg :
        ((('index, 'node) avl_split_t1) -> 'summary) ->
        (('index, 'node) avl_split_t1) list -> 'summary)
      (measure : (('index, 'node) avl_split_t1) -> 'summary)
      (measure_closure :
        (('index, 'node) avl_split_t1) -> 'summary)
      (repr :
        (('carrier, 'index) avl_split_t2) ->
        ('index, 'node, 'summary) avl_split_model_tree)
      (m1 :
        (('carrier, 'index) avl_split_t2) ->
        ('index, 'node) avl_split_model)
      (selected :
        'selector ->
        ((('index, 'node) avl_split_t1) avl_split_split) -> bool)
      (selection_possible :
        'selector ->
        (('index, 'node) avl_split_t1) list -> bool)
      (s : 'selector)
      (t3 : ('carrier, 'index) avl_split_t2)
      (o1 :
        ('carrier, 'index, 'node, 'summary) avl_split_view).
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
         avl_split_balanced balancing agg measure_closure
           (repr self) /\
         avl_split_model_seq (m1 self) =
           avl_split_seq_model (repr self) /\
         avl_split_model_hgt (m1 self) =
           avl_split_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      (!selector.
         selection_possible selector [] ==>
         selected selector (AvlSplitSplit [] NONE [])) ==>
      selection_possible s (avl_split_model_seq (m1 t3)) ==>
      (case o1 of
         AvlSplitEmpty =>
           avl_split_model_hgt (m1 t3) = 0 /\
           avl_split_model_seq (m1 t3) = []
       | AvlSplitNode left root right height summary =>
           avl_split_model_seq (m1 t3) =
             node_model
               (avl_split_model_seq (m1 left))
               root
               (avl_split_model_seq (m1 right)) /\
           summary =
             agg measure_closure
               (avl_split_model_seq (m1 t3)) /\
           -(&balancing) <=
             avl_split_model_hgt (m1 left) -
             avl_split_model_hgt (m1 right) /\
           avl_split_model_hgt (m1 left) -
             avl_split_model_hgt (m1 right) <= &balancing /\
           avl_split_model_hgt (m1 t3) = &height /\
           &height =
             1 +
             (if avl_split_model_hgt (m1 left) <
                 avl_split_model_hgt (m1 right)
              then avl_split_model_hgt (m1 right)
              else avl_split_model_hgt (m1 left)))
      ==>
      (case o1 of
         AvlSplitEmpty =>
           let empty_split =
             (AvlSplitSplit [] NONE [] :
               ((('index, 'node) avl_split_t1) avl_split_split))
           in
             (selected s empty_split /\
              avl_split_rebuild empty_split =
                avl_split_model_seq (m1 t3)) /\
             avl_split_model_seq (m1 t3) =
               avl_split_split_left empty_split /\
             avl_split_model_seq (m1 t3) =
               avl_split_split_right empty_split /\
             avl_split_split_middle empty_split = NONE
       | AvlSplitNode tree_left tree_root tree_right height summary =>
           let right_seq = avl_split_model_seq (m1 tree_right) in
           let left_seq = avl_split_model_seq (m1 tree_left)
           in
             (selection_possible s
                (node_model left_seq tree_root right_seq) /\
              agg measure_closure
                (avl_split_model_seq (m1 tree_left)) =
                agg measure_closure left_seq /\
              agg measure_closure
                (avl_split_model_seq (m1 tree_right)) =
                agg measure_closure right_seq) /\
             !(part : 'selector avl_split_part_base).
               (case part of
                  AvlSplitHere =>
                    selected s
                      (AvlSplitSplit left_seq
                        (SOME tree_root) right_seq)
                | AvlSplitLeft left_selector =>
                    selection_possible left_selector left_seq /\
                    !split.
                      (selected left_selector split /\
                       avl_split_rebuild split = left_seq)
                      ==>
                      selected s
                        (avl_split_right_extend
                          split tree_root right_seq)
                | AvlSplitRight right_selector =>
                    selection_possible right_selector right_seq /\
                    !split.
                      (selected right_selector split /\
                       avl_split_rebuild split = right_seq)
                      ==>
                      selected s
                        (avl_split_left_extend
                          left_seq tree_root split))
               ==>
               (case part of
                  AvlSplitLeft left_selector =>
                    (((0 : int) <=
                        avl_split_model_hgt (m1 t3) /\
                      avl_split_model_hgt (m1 tree_left) <
                        avl_split_model_hgt (m1 t3)) /\
                     selection_possible left_selector
                       (avl_split_model_seq (m1 tree_left))) /\
                    !split
                      (left_result :
                        ('carrier, 'index) avl_split_t2)
                      (old_middle :
                        (('index, 'node) avl_split_t1) option)
                      (right_result :
                        ('carrier, 'index) avl_split_t2).
                      ((selected left_selector split /\
                        avl_split_rebuild split =
                          avl_split_model_seq (m1 tree_left)) /\
                       avl_split_model_seq (m1 left_result) =
                         avl_split_split_left split /\
                       avl_split_model_seq (m1 right_result) =
                         avl_split_split_right split /\
                       (case old_middle of
                          NONE =>
                            avl_split_split_middle split = NONE
                        | SOME element =>
                            avl_split_split_middle split =
                              SOME element))
                      ==>
                      !joined_result :
                        ('carrier, 'index) avl_split_t2.
                        (avl_split_model_seq (m1 joined_result) =
                           node_model
                             (avl_split_model_seq (m1 right_result))
                             tree_root
                             (avl_split_model_seq (m1 tree_right)) /\
                         (let left_height =
                            avl_split_model_hgt (m1 right_result)
                          in
                          let right_height =
                            avl_split_model_hgt (m1 tree_right)
                          in
                          let expected_height =
                            1 +
                              (if left_height < right_height
                               then right_height
                               else left_height)
                          in
                          let result_height =
                            avl_split_model_hgt (m1 joined_result)
                          in
                            (0 : int) <=
                              expected_height - result_height /\
                            expected_height - result_height <= 1))
                        ==>
                        (selected s
                           (avl_split_right_extend
                             split tree_root
                             (avl_split_model_seq (m1 tree_right))) /\
                         avl_split_rebuild
                           (avl_split_right_extend
                             split tree_root
                             (avl_split_model_seq (m1 tree_right))) =
                           avl_split_model_seq (m1 t3)) /\
                        avl_split_model_seq (m1 left_result) =
                          avl_split_split_left
                            (avl_split_right_extend
                              split tree_root
                              (avl_split_model_seq (m1 tree_right))) /\
                        avl_split_model_seq (m1 joined_result) =
                          avl_split_split_right
                            (avl_split_right_extend
                              split tree_root
                              (avl_split_model_seq (m1 tree_right))) /\
                        (case old_middle of
                           NONE =>
                             avl_split_split_middle
                               (avl_split_right_extend
                                 split tree_root
                                 (avl_split_model_seq (m1 tree_right))) =
                               NONE
                         | SOME element =>
                             avl_split_split_middle
                               (avl_split_right_extend
                                 split tree_root
                                 (avl_split_model_seq (m1 tree_right))) =
                               SOME element)
                | AvlSplitRight right_selector =>
                    (((0 : int) <=
                        avl_split_model_hgt (m1 t3) /\
                      avl_split_model_hgt (m1 tree_right) <
                        avl_split_model_hgt (m1 t3)) /\
                     selection_possible right_selector
                       (avl_split_model_seq (m1 tree_right))) /\
                    !split
                      (left_result :
                        ('carrier, 'index) avl_split_t2)
                      (old_middle :
                        (('index, 'node) avl_split_t1) option)
                      (right_result :
                        ('carrier, 'index) avl_split_t2).
                      ((selected right_selector split /\
                        avl_split_rebuild split =
                          avl_split_model_seq (m1 tree_right)) /\
                       avl_split_model_seq (m1 left_result) =
                         avl_split_split_left split /\
                       avl_split_model_seq (m1 right_result) =
                         avl_split_split_right split /\
                       (case old_middle of
                          NONE =>
                            avl_split_split_middle split = NONE
                        | SOME element =>
                            avl_split_split_middle split =
                              SOME element))
                      ==>
                      !joined_result :
                        ('carrier, 'index) avl_split_t2.
                        (avl_split_model_seq (m1 joined_result) =
                           node_model
                             (avl_split_model_seq (m1 tree_left))
                             tree_root
                             (avl_split_model_seq (m1 left_result)) /\
                         (let left_height =
                            avl_split_model_hgt (m1 tree_left)
                          in
                          let right_height =
                            avl_split_model_hgt (m1 left_result)
                          in
                          let expected_height =
                            1 +
                              (if left_height < right_height
                               then right_height
                               else left_height)
                          in
                          let result_height =
                            avl_split_model_hgt (m1 joined_result)
                          in
                            (0 : int) <=
                              expected_height - result_height /\
                            expected_height - result_height <= 1))
                        ==>
                        (selected s
                           (avl_split_left_extend
                             (avl_split_model_seq (m1 tree_left))
                             tree_root split) /\
                         avl_split_rebuild
                           (avl_split_left_extend
                             (avl_split_model_seq (m1 tree_left))
                             tree_root split) =
                           avl_split_model_seq (m1 t3)) /\
                        avl_split_model_seq (m1 joined_result) =
                          avl_split_split_left
                            (avl_split_left_extend
                              (avl_split_model_seq (m1 tree_left))
                              tree_root split) /\
                        avl_split_model_seq (m1 right_result) =
                          avl_split_split_right
                            (avl_split_left_extend
                              (avl_split_model_seq (m1 tree_left))
                              tree_root split) /\
                        (case old_middle of
                           NONE =>
                             avl_split_split_middle
                               (avl_split_left_extend
                                 (avl_split_model_seq (m1 tree_left))
                                 tree_root split) =
                               NONE
                         | SOME element =>
                             avl_split_split_middle
                               (avl_split_left_extend
                                 (avl_split_model_seq (m1 tree_left))
                                 tree_root split) =
                               SOME element)
                | AvlSplitHere =>
                    (selected s
                       (AvlSplitSplit
                         (avl_split_model_seq (m1 tree_left))
                         (SOME tree_root)
                         (avl_split_model_seq (m1 tree_right))) /\
                     avl_split_rebuild
                       (AvlSplitSplit
                         (avl_split_model_seq (m1 tree_left))
                         (SOME tree_root)
                         (avl_split_model_seq (m1 tree_right))) =
                       avl_split_model_seq (m1 t3)) /\
                    avl_split_model_seq (m1 tree_left) =
                      avl_split_split_left
                        (AvlSplitSplit
                          (avl_split_model_seq (m1 tree_left))
                          (SOME tree_root)
                          (avl_split_model_seq (m1 tree_right))) /\
                    avl_split_model_seq (m1 tree_right) =
                      avl_split_split_right
                        (AvlSplitSplit
                          (avl_split_model_seq (m1 tree_left))
                          (SOME tree_root)
                          (avl_split_model_seq (m1 tree_right))) /\
                    avl_split_split_middle
                      (AvlSplitSplit
                        (avl_split_model_seq (m1 tree_left))
                        (SOME tree_root)
                        (avl_split_model_seq (m1 tree_right))) =
                      SOME tree_root))``;
