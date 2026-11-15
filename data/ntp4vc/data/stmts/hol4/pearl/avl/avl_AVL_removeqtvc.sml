(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_removeqtvc: an AVL-tree removal verification condition
  for selector-guided sequence splits, preserving rebuilt sequences and
  bounding height decrease in the empty, left, right, and root cases. This
  file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus avl_remove_t1
  and avl_remove_t2 are bijective indexed wrappers of their arbitrary
  underlying carriers for the quantified source type instance.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_remove_t1 = AvlRemoveT1 ('index -> unit) 'node
End

Datatype:
  avl_remove_t2 = AvlRemoveT2 ('index -> unit) 'carrier
End

Datatype:
  avl_remove_model_tree =
    AvlRemoveModelEmpty
  | AvlRemoveModelNode avl_remove_model_tree
      (('index, 'node) avl_remove_t1)
      avl_remove_model_tree num 'summary
End

Datatype:
  avl_remove_model =
    AvlRemoveModel ((('index, 'node) avl_remove_t1) list) int
End

Datatype:
  avl_remove_view =
    AvlRemoveEmpty
  | AvlRemoveNode
      (('carrier, 'index) avl_remove_t2)
      (('index, 'node) avl_remove_t1)
      (('carrier, 'index) avl_remove_t2)
      num 'summary
End

Datatype:
  avl_remove_split = AvlRemoveSplit ('a list) ('a option) ('a list)
End

Datatype:
  avl_remove_part_base =
    AvlRemoveLeft 'selector
  | AvlRemoveRight 'selector
  | AvlRemoveHere
End

val avl_remove_model_seq_def = Define `
  avl_remove_model_seq (AvlRemoveModel elements height) = elements`;

val avl_remove_model_hgt_def = Define `
  avl_remove_model_hgt (AvlRemoveModel elements height) = height`;

val avl_remove_split_left_def = Define `
  avl_remove_split_left (AvlRemoveSplit left middle right) = left`;

val avl_remove_split_middle_def = Define `
  avl_remove_split_middle (AvlRemoveSplit left middle right) = middle`;

val avl_remove_split_right_def = Define `
  avl_remove_split_right (AvlRemoveSplit left middle right) = right`;

val avl_remove_option_to_seq_def = Define `
  (avl_remove_option_to_seq NONE = []) /\
  (avl_remove_option_to_seq (SOME element) = [element])`;

val avl_remove_rebuild_def = Define `
  avl_remove_rebuild split =
    APPEND
      (APPEND
        (avl_remove_split_left split)
        (avl_remove_option_to_seq (avl_remove_split_middle split)))
      (avl_remove_split_right split)`;

val avl_remove_left_extend_def = Define `
  avl_remove_left_extend left root split =
    AvlRemoveSplit
      (APPEND left (root :: avl_remove_split_left split))
      (avl_remove_split_middle split)
      (avl_remove_split_right split)`;

val avl_remove_right_extend_def = Define `
  avl_remove_right_extend split root right =
    AvlRemoveSplit
      (avl_remove_split_left split)
      (avl_remove_split_middle split)
      (APPEND (avl_remove_split_right split) (root :: right))`;

val avl_remove_seq_model_def = Define `
  (avl_remove_seq_model AvlRemoveModelEmpty = []) /\
  (avl_remove_seq_model
      (AvlRemoveModelNode left root right height summary) =
     APPEND (avl_remove_seq_model left)
       (root :: avl_remove_seq_model right))`;

val avl_remove_real_height_def = Define `
  (avl_remove_real_height AvlRemoveModelEmpty = (0 : int)) /\
  (avl_remove_real_height
      (AvlRemoveModelNode left root right height summary) =
     1 +
       (if avl_remove_real_height left <
           avl_remove_real_height right
        then avl_remove_real_height right
        else avl_remove_real_height left))`;

val avl_remove_balanced_def = Define `
  (avl_remove_balanced balancing agg measure_closure
      AvlRemoveModelEmpty = T) /\
  (avl_remove_balanced balancing agg measure_closure
      (AvlRemoveModelNode left root right height summary) =
     (&height =
        avl_remove_real_height
          (AvlRemoveModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_remove_seq_model
            (AvlRemoveModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_remove_real_height right -
        avl_remove_real_height left /\
      avl_remove_real_height right -
        avl_remove_real_height left <= &balancing /\
      avl_remove_balanced balancing agg measure_closure left /\
      avl_remove_balanced balancing agg measure_closure right))`;

val avl_remove_vc =
  ``let node_model =
      \left : (('index, 'node) avl_remove_t1) list.
      \root : ('index, 'node) avl_remove_t1.
      \right : (('index, 'node) avl_remove_t1) list.
        APPEND left (root :: right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg :
        ((('index, 'node) avl_remove_t1) -> 'summary) ->
        (('index, 'node) avl_remove_t1) list -> 'summary)
      (measure : (('index, 'node) avl_remove_t1) -> 'summary)
      (measure_closure :
        (('index, 'node) avl_remove_t1) -> 'summary)
      (repr :
        (('carrier, 'index) avl_remove_t2) ->
        ('index, 'node, 'summary) avl_remove_model_tree)
      (m1 :
        (('carrier, 'index) avl_remove_t2) ->
        ('index, 'node) avl_remove_model)
      (selected :
        'selector ->
        ((('index, 'node) avl_remove_t1) avl_remove_split) -> bool)
      (selection_possible :
        'selector ->
        (('index, 'node) avl_remove_t1) list -> bool)
      (s : 'selector)
      (t3 : ('carrier, 'index) avl_remove_t2)
      (o1 :
        ('carrier, 'index, 'node, 'summary) avl_remove_view).
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
         avl_remove_balanced balancing agg measure_closure
           (repr self) /\
         avl_remove_model_seq (m1 self) =
           avl_remove_seq_model (repr self) /\
         avl_remove_model_hgt (m1 self) =
           avl_remove_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      (!selector.
         selection_possible selector [] ==>
         selected selector (AvlRemoveSplit [] NONE [])) ==>
      selection_possible s (avl_remove_model_seq (m1 t3)) ==>
      (case o1 of
         AvlRemoveEmpty =>
           avl_remove_model_hgt (m1 t3) = 0 /\
           avl_remove_model_seq (m1 t3) = []
       | AvlRemoveNode left root right height summary =>
           avl_remove_model_seq (m1 t3) =
             node_model
               (avl_remove_model_seq (m1 left))
               root
               (avl_remove_model_seq (m1 right)) /\
           summary =
             agg measure_closure
               (avl_remove_model_seq (m1 t3)) /\
           -(&balancing) <=
             avl_remove_model_hgt (m1 left) -
             avl_remove_model_hgt (m1 right) /\
           avl_remove_model_hgt (m1 left) -
             avl_remove_model_hgt (m1 right) <= &balancing /\
           avl_remove_model_hgt (m1 t3) = &height /\
           &height =
             1 +
             (if avl_remove_model_hgt (m1 left) <
                 avl_remove_model_hgt (m1 right)
              then avl_remove_model_hgt (m1 right)
              else avl_remove_model_hgt (m1 left)))
      ==>
      (case o1 of
         AvlRemoveEmpty =>
           let empty_split =
             (AvlRemoveSplit [] NONE [] :
               ((('index, 'node) avl_remove_t1) avl_remove_split))
           in
             avl_remove_model_seq (m1 t3) =
               APPEND
                 (avl_remove_split_left empty_split)
                 (avl_remove_split_right empty_split) /\
             (selected s empty_split /\
              avl_remove_rebuild empty_split =
                avl_remove_model_seq (m1 t3)) /\
             avl_remove_model_hgt (m1 t3) -
               avl_remove_model_hgt (m1 t3) <= 1 /\
             (0 : int) <=
               avl_remove_model_hgt (m1 t3) -
               avl_remove_model_hgt (m1 t3)
       | AvlRemoveNode tree_left tree_root tree_right height summary =>
           let right_seq = avl_remove_model_seq (m1 tree_right) in
           let left_seq = avl_remove_model_seq (m1 tree_left)
           in
             (selection_possible s
                (node_model left_seq tree_root right_seq) /\
              agg measure_closure
                (avl_remove_model_seq (m1 tree_left)) =
                agg measure_closure left_seq /\
              agg measure_closure
                (avl_remove_model_seq (m1 tree_right)) =
                agg measure_closure right_seq) /\
             !(part : 'selector avl_remove_part_base).
               (case part of
                  AvlRemoveHere =>
                    selected s
                      (AvlRemoveSplit left_seq
                        (SOME tree_root) right_seq)
                | AvlRemoveLeft left_selector =>
                    selection_possible left_selector left_seq /\
                    !split.
                      (selected left_selector split /\
                       avl_remove_rebuild split = left_seq)
                      ==>
                      selected s
                        (avl_remove_right_extend
                          split tree_root right_seq)
                | AvlRemoveRight right_selector =>
                    selection_possible right_selector right_seq /\
                    !split.
                      (selected right_selector split /\
                       avl_remove_rebuild split = right_seq)
                      ==>
                      selected s
                        (avl_remove_left_extend
                          left_seq tree_root split))
               ==>
               (case part of
                  AvlRemoveLeft left_selector =>
                    (((0 : int) <=
                        avl_remove_model_hgt (m1 t3) /\
                      avl_remove_model_hgt (m1 tree_left) <
                        avl_remove_model_hgt (m1 t3)) /\
                     selection_possible left_selector
                       (avl_remove_model_seq (m1 tree_left))) /\
                    !split
                      (new_left :
                        ('carrier, 'index) avl_remove_t2).
                      (avl_remove_model_seq (m1 new_left) =
                         APPEND
                           (avl_remove_split_left split)
                           (avl_remove_split_right split) /\
                       (selected left_selector split /\
                        avl_remove_rebuild split =
                          avl_remove_model_seq (m1 tree_left)) /\
                       avl_remove_model_hgt (m1 tree_left) -
                         avl_remove_model_hgt (m1 new_left) <= 1 /\
                       (0 : int) <=
                         avl_remove_model_hgt (m1 tree_left) -
                         avl_remove_model_hgt (m1 new_left))
                      ==>
                      (-(&balancing) - 1 <=
                         avl_remove_model_hgt (m1 new_left) -
                         avl_remove_model_hgt (m1 tree_right) /\
                       avl_remove_model_hgt (m1 new_left) -
                         avl_remove_model_hgt (m1 tree_right) <=
                         &balancing + 1) /\
                      !result : ('carrier, 'index) avl_remove_t2.
                        (avl_remove_model_seq (m1 result) =
                           node_model
                             (avl_remove_model_seq (m1 new_left))
                             tree_root
                             (avl_remove_model_seq (m1 tree_right)) /\
                         (let left_height =
                            avl_remove_model_hgt (m1 new_left) in
                          let right_height =
                            avl_remove_model_hgt (m1 tree_right) in
                          let expected_height =
                            1 +
                              (if left_height < right_height
                               then right_height
                               else left_height) in
                          let result_height =
                            avl_remove_model_hgt (m1 result)
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
                        avl_remove_model_seq (m1 result) =
                          APPEND
                            (avl_remove_split_left
                              (avl_remove_right_extend split tree_root
                                (avl_remove_model_seq
                                  (m1 tree_right))))
                            (avl_remove_split_right
                              (avl_remove_right_extend split tree_root
                                (avl_remove_model_seq
                                  (m1 tree_right)))) /\
                        (selected s
                           (avl_remove_right_extend split tree_root
                             (avl_remove_model_seq (m1 tree_right))) /\
                         avl_remove_rebuild
                           (avl_remove_right_extend split tree_root
                             (avl_remove_model_seq (m1 tree_right))) =
                           avl_remove_model_seq (m1 t3)) /\
                        avl_remove_model_hgt (m1 t3) -
                          avl_remove_model_hgt (m1 result) <= 1 /\
                        (0 : int) <=
                          avl_remove_model_hgt (m1 t3) -
                          avl_remove_model_hgt (m1 result)
                | AvlRemoveRight right_selector =>
                    (((0 : int) <=
                        avl_remove_model_hgt (m1 t3) /\
                      avl_remove_model_hgt (m1 tree_right) <
                        avl_remove_model_hgt (m1 t3)) /\
                     selection_possible right_selector
                       (avl_remove_model_seq (m1 tree_right))) /\
                    !split
                      (new_right :
                        ('carrier, 'index) avl_remove_t2).
                      (avl_remove_model_seq (m1 new_right) =
                         APPEND
                           (avl_remove_split_left split)
                           (avl_remove_split_right split) /\
                       (selected right_selector split /\
                        avl_remove_rebuild split =
                          avl_remove_model_seq (m1 tree_right)) /\
                       avl_remove_model_hgt (m1 tree_right) -
                         avl_remove_model_hgt (m1 new_right) <= 1 /\
                       (0 : int) <=
                         avl_remove_model_hgt (m1 tree_right) -
                         avl_remove_model_hgt (m1 new_right))
                      ==>
                      (-(&balancing) - 1 <=
                         avl_remove_model_hgt (m1 tree_left) -
                         avl_remove_model_hgt (m1 new_right) /\
                       avl_remove_model_hgt (m1 tree_left) -
                         avl_remove_model_hgt (m1 new_right) <=
                         &balancing + 1) /\
                      !result : ('carrier, 'index) avl_remove_t2.
                        (avl_remove_model_seq (m1 result) =
                           node_model
                             (avl_remove_model_seq (m1 tree_left))
                             tree_root
                             (avl_remove_model_seq (m1 new_right)) /\
                         (let left_height =
                            avl_remove_model_hgt (m1 tree_left) in
                          let right_height =
                            avl_remove_model_hgt (m1 new_right) in
                          let expected_height =
                            1 +
                              (if left_height < right_height
                               then right_height
                               else left_height) in
                          let result_height =
                            avl_remove_model_hgt (m1 result)
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
                        avl_remove_model_seq (m1 result) =
                          APPEND
                            (avl_remove_split_left
                              (avl_remove_left_extend
                                (avl_remove_model_seq (m1 tree_left))
                                tree_root split))
                            (avl_remove_split_right
                              (avl_remove_left_extend
                                (avl_remove_model_seq (m1 tree_left))
                                tree_root split)) /\
                        (selected s
                           (avl_remove_left_extend
                             (avl_remove_model_seq (m1 tree_left))
                             tree_root split) /\
                         avl_remove_rebuild
                           (avl_remove_left_extend
                             (avl_remove_model_seq (m1 tree_left))
                             tree_root split) =
                           avl_remove_model_seq (m1 t3)) /\
                        avl_remove_model_hgt (m1 t3) -
                          avl_remove_model_hgt (m1 result) <= 1 /\
                        (0 : int) <=
                          avl_remove_model_hgt (m1 t3) -
                          avl_remove_model_hgt (m1 result)
                | AvlRemoveHere =>
                    (-(&balancing) <=
                       avl_remove_model_hgt (m1 tree_left) -
                       avl_remove_model_hgt (m1 tree_right) /\
                     avl_remove_model_hgt (m1 tree_left) -
                       avl_remove_model_hgt (m1 tree_right) <=
                       &balancing) /\
                    !result : ('carrier, 'index) avl_remove_t2.
                      (avl_remove_model_seq (m1 result) =
                         APPEND
                           (avl_remove_model_seq (m1 tree_left))
                           (avl_remove_model_seq (m1 tree_right)) /\
                       (let left_height =
                          avl_remove_model_hgt (m1 tree_left) in
                        let right_height =
                          avl_remove_model_hgt (m1 tree_right) in
                        let expected_height =
                          1 +
                            (if left_height < right_height
                             then right_height
                             else left_height)
                        in
                          expected_height -
                            avl_remove_model_hgt (m1 result) <= 1 /\
                          (0 : int) <=
                            expected_height -
                            avl_remove_model_hgt (m1 result))
                      ==>
                      avl_remove_model_seq (m1 result) =
                        APPEND
                          (avl_remove_split_left
                            (AvlRemoveSplit
                              (avl_remove_model_seq (m1 tree_left))
                              (SOME tree_root)
                              (avl_remove_model_seq (m1 tree_right))))
                          (avl_remove_split_right
                            (AvlRemoveSplit
                              (avl_remove_model_seq (m1 tree_left))
                              (SOME tree_root)
                              (avl_remove_model_seq (m1 tree_right)))) /\
                      (selected s
                         (AvlRemoveSplit
                           (avl_remove_model_seq (m1 tree_left))
                           (SOME tree_root)
                           (avl_remove_model_seq (m1 tree_right))) /\
                       avl_remove_rebuild
                         (AvlRemoveSplit
                           (avl_remove_model_seq (m1 tree_left))
                           (SOME tree_root)
                           (avl_remove_model_seq (m1 tree_right))) =
                         avl_remove_model_seq (m1 t3)) /\
                      avl_remove_model_hgt (m1 t3) -
                        avl_remove_model_hgt (m1 result) <= 1 /\
                      (0 : int) <=
                        avl_remove_model_hgt (m1 t3) -
                        avl_remove_model_hgt (m1 result))))``;
