(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_extractqtvc: an AVL-tree extraction verification
  condition for selector-guided sequence splits, preserving rebuilt sequences,
  optional selected elements, and bounded height decrease in the empty, left,
  right, and root cases. This file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus
  avl_extract_t1 and avl_extract_t2 are bijective indexed wrappers of their
  arbitrary underlying carriers for the quantified source type instance.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_extract_t1 = AvlExtractT1 ('index -> unit) 'node
End

Datatype:
  avl_extract_t2 = AvlExtractT2 ('index -> unit) 'carrier
End

Datatype:
  avl_extract_model_tree =
    AvlExtractModelEmpty
  | AvlExtractModelNode avl_extract_model_tree
      (('index, 'node) avl_extract_t1)
      avl_extract_model_tree num 'summary
End

Datatype:
  avl_extract_model =
    AvlExtractModel ((('index, 'node) avl_extract_t1) list) int
End

Datatype:
  avl_extract_view =
    AvlExtractEmpty
  | AvlExtractNode
      (('carrier, 'index) avl_extract_t2)
      (('index, 'node) avl_extract_t1)
      (('carrier, 'index) avl_extract_t2)
      num 'summary
End

Datatype:
  avl_extract_split = AvlExtractSplit ('a list) ('a option) ('a list)
End

Datatype:
  avl_extract_part_base =
    AvlExtractLeft 'selector
  | AvlExtractRight 'selector
  | AvlExtractHere
End

val avl_extract_model_seq_def = Define `
  avl_extract_model_seq (AvlExtractModel elements height) = elements`;

val avl_extract_model_hgt_def = Define `
  avl_extract_model_hgt (AvlExtractModel elements height) = height`;

val avl_extract_split_left_def = Define `
  avl_extract_split_left (AvlExtractSplit left middle right) = left`;

val avl_extract_split_middle_def = Define `
  avl_extract_split_middle (AvlExtractSplit left middle right) = middle`;

val avl_extract_split_right_def = Define `
  avl_extract_split_right (AvlExtractSplit left middle right) = right`;

val avl_extract_option_to_seq_def = Define `
  (avl_extract_option_to_seq NONE = []) /\
  (avl_extract_option_to_seq (SOME element) = [element])`;

val avl_extract_rebuild_def = Define `
  avl_extract_rebuild split =
    APPEND
      (APPEND
        (avl_extract_split_left split)
        (avl_extract_option_to_seq (avl_extract_split_middle split)))
      (avl_extract_split_right split)`;

val avl_extract_left_extend_def = Define `
  avl_extract_left_extend left root split =
    AvlExtractSplit
      (APPEND left (root :: avl_extract_split_left split))
      (avl_extract_split_middle split)
      (avl_extract_split_right split)`;

val avl_extract_right_extend_def = Define `
  avl_extract_right_extend split root right =
    AvlExtractSplit
      (avl_extract_split_left split)
      (avl_extract_split_middle split)
      (APPEND (avl_extract_split_right split) (root :: right))`;

val avl_extract_seq_model_def = Define `
  (avl_extract_seq_model AvlExtractModelEmpty = []) /\
  (avl_extract_seq_model
      (AvlExtractModelNode left root right height summary) =
     APPEND (avl_extract_seq_model left)
       (root :: avl_extract_seq_model right))`;

val avl_extract_real_height_def = Define `
  (avl_extract_real_height AvlExtractModelEmpty = (0 : int)) /\
  (avl_extract_real_height
      (AvlExtractModelNode left root right height summary) =
     1 +
       (if avl_extract_real_height left <
           avl_extract_real_height right
        then avl_extract_real_height right
        else avl_extract_real_height left))`;

val avl_extract_balanced_def = Define `
  (avl_extract_balanced balancing agg measure_closure
      AvlExtractModelEmpty = T) /\
  (avl_extract_balanced balancing agg measure_closure
      (AvlExtractModelNode left root right height summary) =
     (&height =
        avl_extract_real_height
          (AvlExtractModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_extract_seq_model
            (AvlExtractModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_extract_real_height right -
        avl_extract_real_height left /\
      avl_extract_real_height right -
        avl_extract_real_height left <= &balancing /\
      avl_extract_balanced balancing agg measure_closure left /\
      avl_extract_balanced balancing agg measure_closure right))`;

val avl_extract_vc =
  ``let node_model =
      \left : (('index, 'node) avl_extract_t1) list.
      \root : ('index, 'node) avl_extract_t1.
      \right : (('index, 'node) avl_extract_t1) list.
        APPEND left (root :: right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg :
        ((('index, 'node) avl_extract_t1) -> 'summary) ->
        (('index, 'node) avl_extract_t1) list -> 'summary)
      (measure : (('index, 'node) avl_extract_t1) -> 'summary)
      (measure_closure :
        (('index, 'node) avl_extract_t1) -> 'summary)
      (repr :
        (('carrier, 'index) avl_extract_t2) ->
        ('index, 'node, 'summary) avl_extract_model_tree)
      (m1 :
        (('carrier, 'index) avl_extract_t2) ->
        ('index, 'node) avl_extract_model)
      (selected :
        'selector ->
        ((('index, 'node) avl_extract_t1) avl_extract_split) -> bool)
      (selection_possible :
        'selector ->
        (('index, 'node) avl_extract_t1) list -> bool)
      (s : 'selector)
      (t3 : ('carrier, 'index) avl_extract_t2)
      (o1 :
        ('carrier, 'index, 'node, 'summary) avl_extract_view).
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
         avl_extract_balanced balancing agg measure_closure
           (repr self) /\
         avl_extract_model_seq (m1 self) =
           avl_extract_seq_model (repr self) /\
         avl_extract_model_hgt (m1 self) =
           avl_extract_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      (!selector.
         selection_possible selector [] ==>
         selected selector (AvlExtractSplit [] NONE [])) ==>
      selection_possible s (avl_extract_model_seq (m1 t3)) ==>
      (case o1 of
         AvlExtractEmpty =>
           avl_extract_model_hgt (m1 t3) = 0 /\
           avl_extract_model_seq (m1 t3) = []
       | AvlExtractNode left root right height summary =>
           avl_extract_model_seq (m1 t3) =
             node_model
               (avl_extract_model_seq (m1 left))
               root
               (avl_extract_model_seq (m1 right)) /\
           summary =
             agg measure_closure
               (avl_extract_model_seq (m1 t3)) /\
           -(&balancing) <=
             avl_extract_model_hgt (m1 left) -
             avl_extract_model_hgt (m1 right) /\
           avl_extract_model_hgt (m1 left) -
             avl_extract_model_hgt (m1 right) <= &balancing /\
           avl_extract_model_hgt (m1 t3) = &height /\
           &height =
             1 +
             (if avl_extract_model_hgt (m1 left) <
                 avl_extract_model_hgt (m1 right)
              then avl_extract_model_hgt (m1 right)
              else avl_extract_model_hgt (m1 left)))
      ==>
      (case o1 of
         AvlExtractEmpty =>
           let empty_split =
             (AvlExtractSplit [] NONE [] :
               ((('index, 'node) avl_extract_t1) avl_extract_split))
           in
             (selected s empty_split /\
              avl_extract_rebuild empty_split =
                avl_extract_model_seq (m1 t3)) /\
             avl_extract_model_seq (m1 t3) =
               APPEND
                 (avl_extract_split_left empty_split)
                 (avl_extract_split_right empty_split) /\
             (avl_extract_model_hgt (m1 t3) -
                avl_extract_model_hgt (m1 t3) <= 1 /\
              (0 : int) <=
                avl_extract_model_hgt (m1 t3) -
                avl_extract_model_hgt (m1 t3)) /\
             avl_extract_split_middle empty_split = NONE
       | AvlExtractNode tree_left tree_root tree_right height summary =>
           let right_seq = avl_extract_model_seq (m1 tree_right) in
           let left_seq = avl_extract_model_seq (m1 tree_left)
           in
             (selection_possible s
                (node_model left_seq tree_root right_seq) /\
              agg measure_closure
                (avl_extract_model_seq (m1 tree_left)) =
                agg measure_closure left_seq /\
              agg measure_closure
                (avl_extract_model_seq (m1 tree_right)) =
                agg measure_closure right_seq) /\
             !(part : 'selector avl_extract_part_base).
               (case part of
                  AvlExtractHere =>
                    selected s
                      (AvlExtractSplit left_seq
                        (SOME tree_root) right_seq)
                | AvlExtractLeft left_selector =>
                    selection_possible left_selector left_seq /\
                    !split.
                      (selected left_selector split /\
                       avl_extract_rebuild split = left_seq)
                      ==>
                      selected s
                        (avl_extract_right_extend
                          split tree_root right_seq)
                | AvlExtractRight right_selector =>
                    selection_possible right_selector right_seq /\
                    !split.
                      (selected right_selector split /\
                       avl_extract_rebuild split = right_seq)
                      ==>
                      selected s
                        (avl_extract_left_extend
                          left_seq tree_root split))
               ==>
               (case part of
                  AvlExtractLeft left_selector =>
                    (((0 : int) <=
                        avl_extract_model_hgt (m1 t3) /\
                      avl_extract_model_hgt (m1 tree_left) <
                        avl_extract_model_hgt (m1 t3)) /\
                     selection_possible left_selector
                       (avl_extract_model_seq (m1 tree_left))) /\
                    !split
                      (old_middle :
                        (('index, 'node) avl_extract_t1) option)
                      (new_left :
                        ('carrier, 'index) avl_extract_t2).
                      ((selected left_selector split /\
                        avl_extract_rebuild split =
                          avl_extract_model_seq (m1 tree_left)) /\
                       avl_extract_model_seq (m1 new_left) =
                         APPEND
                           (avl_extract_split_left split)
                           (avl_extract_split_right split) /\
                       (avl_extract_model_hgt (m1 tree_left) -
                          avl_extract_model_hgt (m1 new_left) <= 1 /\
                        (0 : int) <=
                          avl_extract_model_hgt (m1 tree_left) -
                          avl_extract_model_hgt (m1 new_left)) /\
                       (case old_middle of
                          NONE =>
                            avl_extract_split_middle split = NONE
                        | SOME element =>
                            avl_extract_split_middle split =
                              SOME element))
                      ==>
                      (-(&balancing) - 1 <=
                         avl_extract_model_hgt (m1 new_left) -
                         avl_extract_model_hgt (m1 tree_right) /\
                       avl_extract_model_hgt (m1 new_left) -
                         avl_extract_model_hgt (m1 tree_right) <=
                         &balancing + 1) /\
                      !result : ('carrier, 'index) avl_extract_t2.
                        (avl_extract_model_seq (m1 result) =
                           node_model
                             (avl_extract_model_seq (m1 new_left))
                             tree_root
                             (avl_extract_model_seq (m1 tree_right)) /\
                         (let left_height =
                            avl_extract_model_hgt (m1 new_left) in
                          let right_height =
                            avl_extract_model_hgt (m1 tree_right) in
                          let expected_height =
                            1 +
                              (if left_height < right_height
                               then right_height
                               else left_height) in
                          let result_height =
                            avl_extract_model_hgt (m1 result)
                          in
                            ((0 : int) <=
                               expected_height - result_height /\
                             expected_height - result_height <= 1) /\
                            ((-(&balancing) <=
                                left_height - right_height /\
                              left_height - right_height <=
                                &balancing)
                             ==>
                             expected_height = result_height)))
                        ==>
                        (selected s
                           (avl_extract_right_extend split tree_root
                             (avl_extract_model_seq (m1 tree_right))) /\
                         avl_extract_rebuild
                           (avl_extract_right_extend split tree_root
                             (avl_extract_model_seq (m1 tree_right))) =
                           avl_extract_model_seq (m1 t3)) /\
                        avl_extract_model_seq (m1 result) =
                          APPEND
                            (avl_extract_split_left
                              (avl_extract_right_extend split tree_root
                                (avl_extract_model_seq
                                  (m1 tree_right))))
                            (avl_extract_split_right
                              (avl_extract_right_extend split tree_root
                                (avl_extract_model_seq
                                  (m1 tree_right)))) /\
                        (avl_extract_model_hgt (m1 t3) -
                           avl_extract_model_hgt (m1 result) <= 1 /\
                         (0 : int) <=
                           avl_extract_model_hgt (m1 t3) -
                           avl_extract_model_hgt (m1 result)) /\
                        (case old_middle of
                           NONE =>
                             avl_extract_split_middle
                               (avl_extract_right_extend split tree_root
                                 (avl_extract_model_seq
                                   (m1 tree_right))) = NONE
                         | SOME element =>
                             avl_extract_split_middle
                               (avl_extract_right_extend split tree_root
                                 (avl_extract_model_seq
                                   (m1 tree_right))) = SOME element)
                | AvlExtractRight right_selector =>
                    (((0 : int) <=
                        avl_extract_model_hgt (m1 t3) /\
                      avl_extract_model_hgt (m1 tree_right) <
                        avl_extract_model_hgt (m1 t3)) /\
                     selection_possible right_selector
                       (avl_extract_model_seq (m1 tree_right))) /\
                    !split
                      (old_middle :
                        (('index, 'node) avl_extract_t1) option)
                      (new_right :
                        ('carrier, 'index) avl_extract_t2).
                      ((selected right_selector split /\
                        avl_extract_rebuild split =
                          avl_extract_model_seq (m1 tree_right)) /\
                       avl_extract_model_seq (m1 new_right) =
                         APPEND
                           (avl_extract_split_left split)
                           (avl_extract_split_right split) /\
                       (avl_extract_model_hgt (m1 tree_right) -
                          avl_extract_model_hgt (m1 new_right) <= 1 /\
                        (0 : int) <=
                          avl_extract_model_hgt (m1 tree_right) -
                          avl_extract_model_hgt (m1 new_right)) /\
                       (case old_middle of
                          NONE =>
                            avl_extract_split_middle split = NONE
                        | SOME element =>
                            avl_extract_split_middle split =
                              SOME element))
                      ==>
                      (-(&balancing) - 1 <=
                         avl_extract_model_hgt (m1 tree_left) -
                         avl_extract_model_hgt (m1 new_right) /\
                       avl_extract_model_hgt (m1 tree_left) -
                         avl_extract_model_hgt (m1 new_right) <=
                         &balancing + 1) /\
                      !result : ('carrier, 'index) avl_extract_t2.
                        (avl_extract_model_seq (m1 result) =
                           node_model
                             (avl_extract_model_seq (m1 tree_left))
                             tree_root
                             (avl_extract_model_seq (m1 new_right)) /\
                         (let left_height =
                            avl_extract_model_hgt (m1 tree_left) in
                          let right_height =
                            avl_extract_model_hgt (m1 new_right) in
                          let expected_height =
                            1 +
                              (if left_height < right_height
                               then right_height
                               else left_height) in
                          let result_height =
                            avl_extract_model_hgt (m1 result)
                          in
                            ((0 : int) <=
                               expected_height - result_height /\
                             expected_height - result_height <= 1) /\
                            ((-(&balancing) <=
                                left_height - right_height /\
                              left_height - right_height <=
                                &balancing)
                             ==>
                             expected_height = result_height)))
                        ==>
                        (selected s
                           (avl_extract_left_extend
                             (avl_extract_model_seq (m1 tree_left))
                             tree_root split) /\
                         avl_extract_rebuild
                           (avl_extract_left_extend
                             (avl_extract_model_seq (m1 tree_left))
                             tree_root split) =
                           avl_extract_model_seq (m1 t3)) /\
                        avl_extract_model_seq (m1 result) =
                          APPEND
                            (avl_extract_split_left
                              (avl_extract_left_extend
                                (avl_extract_model_seq (m1 tree_left))
                                tree_root split))
                            (avl_extract_split_right
                              (avl_extract_left_extend
                                (avl_extract_model_seq (m1 tree_left))
                                tree_root split)) /\
                        (avl_extract_model_hgt (m1 t3) -
                           avl_extract_model_hgt (m1 result) <= 1 /\
                         (0 : int) <=
                           avl_extract_model_hgt (m1 t3) -
                           avl_extract_model_hgt (m1 result)) /\
                        (case old_middle of
                           NONE =>
                             avl_extract_split_middle
                               (avl_extract_left_extend
                                 (avl_extract_model_seq (m1 tree_left))
                                 tree_root split) = NONE
                         | SOME element =>
                             avl_extract_split_middle
                               (avl_extract_left_extend
                                 (avl_extract_model_seq (m1 tree_left))
                                 tree_root split) = SOME element)
                | AvlExtractHere =>
                    (-(&balancing) <=
                       avl_extract_model_hgt (m1 tree_left) -
                       avl_extract_model_hgt (m1 tree_right) /\
                     avl_extract_model_hgt (m1 tree_left) -
                       avl_extract_model_hgt (m1 tree_right) <=
                       &balancing) /\
                    !result : ('carrier, 'index) avl_extract_t2.
                      (avl_extract_model_seq (m1 result) =
                         APPEND
                           (avl_extract_model_seq (m1 tree_left))
                           (avl_extract_model_seq (m1 tree_right)) /\
                       (let left_height =
                          avl_extract_model_hgt (m1 tree_left) in
                        let right_height =
                          avl_extract_model_hgt (m1 tree_right) in
                        let expected_height =
                          1 +
                            (if left_height < right_height
                             then right_height
                             else left_height)
                        in
                          expected_height -
                            avl_extract_model_hgt (m1 result) <= 1 /\
                          (0 : int) <=
                            expected_height -
                            avl_extract_model_hgt (m1 result))
                      ==>
                      (selected s
                         (AvlExtractSplit
                           (avl_extract_model_seq (m1 tree_left))
                           (SOME tree_root)
                           (avl_extract_model_seq (m1 tree_right))) /\
                       avl_extract_rebuild
                         (AvlExtractSplit
                           (avl_extract_model_seq (m1 tree_left))
                           (SOME tree_root)
                           (avl_extract_model_seq (m1 tree_right))) =
                         avl_extract_model_seq (m1 t3)) /\
                      avl_extract_model_seq (m1 result) =
                        APPEND
                          (avl_extract_split_left
                            (AvlExtractSplit
                              (avl_extract_model_seq (m1 tree_left))
                              (SOME tree_root)
                              (avl_extract_model_seq (m1 tree_right))))
                          (avl_extract_split_right
                            (AvlExtractSplit
                              (avl_extract_model_seq (m1 tree_left))
                              (SOME tree_root)
                              (avl_extract_model_seq (m1 tree_right)))) /\
                      (avl_extract_model_hgt (m1 t3) -
                         avl_extract_model_hgt (m1 result) <= 1 /\
                       (0 : int) <=
                         avl_extract_model_hgt (m1 t3) -
                         avl_extract_model_hgt (m1 result)) /\
                      avl_extract_split_middle
                        (AvlExtractSplit
                          (avl_extract_model_seq (m1 tree_left))
                          (SOME tree_root)
                          (avl_extract_model_seq (m1 tree_right))) =
                        SOME tree_root)))``;
