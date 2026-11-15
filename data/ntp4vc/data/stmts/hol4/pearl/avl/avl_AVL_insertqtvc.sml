(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_insertqtvc: a selector-guided AVL-tree insertion
  verification condition preserving sequence splits, rebuilt sequences, and
  the source bounds on height growth in the empty, left, right, and root
  cases. This file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. Thus avl_insert_t1
  and avl_insert_t2 are bijective indexed wrappers of their arbitrary
  underlying carriers for the quantified source type instance.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  avl_insert_t1 = AvlInsertT1 ('index -> unit) 'node
End

Datatype:
  avl_insert_t2 = AvlInsertT2 ('index -> unit) 'carrier
End

Datatype:
  avl_insert_model_tree =
    AvlInsertModelEmpty
  | AvlInsertModelNode avl_insert_model_tree
      (('index, 'node) avl_insert_t1)
      avl_insert_model_tree num 'summary
End

Datatype:
  avl_insert_model =
    AvlInsertModel ((('index, 'node) avl_insert_t1) list) int
End

Datatype:
  avl_insert_view =
    AvlInsertEmpty
  | AvlInsertNode
      (('index, 'carrier) avl_insert_t2)
      (('index, 'node) avl_insert_t1)
      (('index, 'carrier) avl_insert_t2)
      num 'summary
End

Datatype:
  avl_insert_split = AvlInsertSplit ('a list) ('a option) ('a list)
End

Datatype:
  avl_insert_part_base =
    AvlInsertLeft 'selector
  | AvlInsertRight 'selector
  | AvlInsertHere
End

val avl_insert_model_seq_def = Define `
  avl_insert_model_seq (AvlInsertModel elements height) = elements`;

val avl_insert_model_hgt_def = Define `
  avl_insert_model_hgt (AvlInsertModel elements height) = height`;

val avl_insert_split_left_def = Define `
  avl_insert_split_left (AvlInsertSplit left middle right) = left`;

val avl_insert_split_middle_def = Define `
  avl_insert_split_middle (AvlInsertSplit left middle right) = middle`;

val avl_insert_split_right_def = Define `
  avl_insert_split_right (AvlInsertSplit left middle right) = right`;

val avl_insert_option_to_seq_def = Define `
  (avl_insert_option_to_seq NONE = []) /\
  (avl_insert_option_to_seq (SOME element) = [element])`;

val avl_insert_rebuild_def = Define `
  avl_insert_rebuild split =
    APPEND
      (APPEND
        (avl_insert_split_left split)
        (avl_insert_option_to_seq (avl_insert_split_middle split)))
      (avl_insert_split_right split)`;

val avl_insert_left_extend_def = Define `
  avl_insert_left_extend left root split =
    AvlInsertSplit
      (APPEND left (root :: avl_insert_split_left split))
      (avl_insert_split_middle split)
      (avl_insert_split_right split)`;

val avl_insert_right_extend_def = Define `
  avl_insert_right_extend split root right =
    AvlInsertSplit
      (avl_insert_split_left split)
      (avl_insert_split_middle split)
      (APPEND (avl_insert_split_right split) (root :: right))`;

val avl_insert_seq_model_def = Define `
  (avl_insert_seq_model AvlInsertModelEmpty = []) /\
  (avl_insert_seq_model
      (AvlInsertModelNode left root right height summary) =
     APPEND (avl_insert_seq_model left)
       (root :: avl_insert_seq_model right))`;

val avl_insert_real_height_def = Define `
  (avl_insert_real_height AvlInsertModelEmpty = (0 : int)) /\
  (avl_insert_real_height
      (AvlInsertModelNode left root right height summary) =
     1 +
       (if avl_insert_real_height left <
           avl_insert_real_height right
        then avl_insert_real_height right
        else avl_insert_real_height left))`;

val avl_insert_balanced_def = Define `
  (avl_insert_balanced balancing agg measure_closure
      AvlInsertModelEmpty = T) /\
  (avl_insert_balanced balancing agg measure_closure
      (AvlInsertModelNode left root right height summary) =
     (&height =
        avl_insert_real_height
          (AvlInsertModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_insert_seq_model
            (AvlInsertModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_insert_real_height right -
        avl_insert_real_height left /\
      avl_insert_real_height right -
        avl_insert_real_height left <= &balancing /\
      avl_insert_balanced balancing agg measure_closure left /\
      avl_insert_balanced balancing agg measure_closure right))`;

val avl_insert_vc =
  ``let node_model =
      \left : (('index, 'node) avl_insert_t1) list.
      \root : ('index, 'node) avl_insert_t1.
      \right : (('index, 'node) avl_insert_t1) list.
        APPEND left (root :: right)
    in
    !(balancing : num)
      (zero : 'summary)
      (op : 'summary -> 'summary -> 'summary)
      (agg :
        ((('index, 'node) avl_insert_t1) -> 'summary) ->
        (('index, 'node) avl_insert_t1) list -> 'summary)
      (measure : (('index, 'node) avl_insert_t1) -> 'summary)
      (measure_closure :
        (('index, 'node) avl_insert_t1) -> 'summary)
      (repr :
        (('index, 'carrier) avl_insert_t2) ->
        ('index, 'node, 'summary) avl_insert_model_tree)
      (m1 :
        (('index, 'carrier) avl_insert_t2) ->
        ('index, 'node) avl_insert_model)
      (selected :
        'selector ->
        ((('index, 'node) avl_insert_t1) avl_insert_split) -> bool)
      (selection_possible :
        'selector ->
        (('index, 'node) avl_insert_t1) list -> bool)
      (s : 'selector)
      (t3 : ('index, 'carrier) avl_insert_t2)
      (o1 :
        ('carrier, 'index, 'node, 'summary) avl_insert_view)
      (d : ('index, 'node) avl_insert_t1).
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
         avl_insert_balanced balancing agg measure_closure
           (repr self) /\
         avl_insert_model_seq (m1 self) =
           avl_insert_seq_model (repr self) /\
         avl_insert_model_hgt (m1 self) =
           avl_insert_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\
         m1 a = m1 b ==>
         a = b) ==>
      (!selector.
         selection_possible selector [] ==>
         selected selector (AvlInsertSplit [] NONE [])) ==>
      selection_possible s (avl_insert_model_seq (m1 t3)) ==>
      (case o1 of
         AvlInsertEmpty =>
           avl_insert_model_hgt (m1 t3) = 0 /\
           avl_insert_model_seq (m1 t3) = []
       | AvlInsertNode left root right height summary =>
           avl_insert_model_seq (m1 t3) =
             node_model
               (avl_insert_model_seq (m1 left))
               root
               (avl_insert_model_seq (m1 right)) /\
           summary =
             agg measure_closure
               (avl_insert_model_seq (m1 t3)) /\
           -(&balancing) <=
             avl_insert_model_hgt (m1 left) -
             avl_insert_model_hgt (m1 right) /\
           avl_insert_model_hgt (m1 left) -
             avl_insert_model_hgt (m1 right) <= &balancing /\
           avl_insert_model_hgt (m1 t3) = &height /\
           &height =
             1 +
             (if avl_insert_model_hgt (m1 left) <
                 avl_insert_model_hgt (m1 right)
              then avl_insert_model_hgt (m1 right)
              else avl_insert_model_hgt (m1 left)))
      ==>
      (case o1 of
         AvlInsertEmpty =>
           !result : ('index, 'carrier) avl_insert_t2.
             (avl_insert_model_seq (m1 result) = [d] /\
              avl_insert_model_hgt (m1 result) = 1)
             ==>
             let empty_split =
               (AvlInsertSplit [] NONE [] :
                 ((('index, 'node) avl_insert_t1) avl_insert_split))
             in
               avl_insert_model_seq (m1 result) =
                 node_model
                   (avl_insert_split_left empty_split)
                   d
                   (avl_insert_split_right empty_split) /\
               (selected s empty_split /\
                avl_insert_rebuild empty_split =
                  avl_insert_model_seq (m1 t3)) /\
               avl_insert_model_hgt (m1 result) -
                 avl_insert_model_hgt (m1 t3) <= 1 /\
               0 <=
                 avl_insert_model_hgt (m1 result) -
                 avl_insert_model_hgt (m1 t3)
       | AvlInsertNode tree_left tree_root tree_right height summary =>
           let right_seq = avl_insert_model_seq (m1 tree_right) in
           let left_seq = avl_insert_model_seq (m1 tree_left) in
             (selection_possible s
                (node_model left_seq tree_root right_seq) /\
              agg measure_closure
                (avl_insert_model_seq (m1 tree_left)) =
                agg measure_closure left_seq /\
              agg measure_closure
                (avl_insert_model_seq (m1 tree_right)) =
                agg measure_closure right_seq) /\
             !part : 'selector avl_insert_part_base.
               (case part of
                  AvlInsertHere =>
                    selected s
                      (AvlInsertSplit left_seq
                        (SOME tree_root) right_seq)
                | AvlInsertLeft left_selector =>
                    selection_possible left_selector left_seq /\
                    !split.
                      (selected left_selector split /\
                       avl_insert_rebuild split = left_seq)
                      ==>
                      selected s
                        (avl_insert_right_extend
                          split tree_root right_seq)
                | AvlInsertRight right_selector =>
                    selection_possible right_selector right_seq /\
                    !split.
                      (selected right_selector split /\
                       avl_insert_rebuild split = right_seq)
                      ==>
                      selected s
                        (avl_insert_left_extend
                          left_seq tree_root split))
               ==>
               (case part of
                  AvlInsertLeft left_selector =>
                    ((0 <= avl_insert_model_hgt (m1 t3) /\
                      avl_insert_model_hgt (m1 tree_left) <
                        avl_insert_model_hgt (m1 t3)) /\
                     selection_possible left_selector
                       (avl_insert_model_seq (m1 tree_left))) /\
                    !split
                      (new_left :
                        ('index, 'carrier) avl_insert_t2).
                      (avl_insert_model_seq (m1 new_left) =
                         node_model
                           (avl_insert_split_left split)
                           d
                           (avl_insert_split_right split) /\
                       (selected left_selector split /\
                        avl_insert_rebuild split =
                          avl_insert_model_seq (m1 tree_left)) /\
                       avl_insert_model_hgt (m1 new_left) -
                         avl_insert_model_hgt (m1 tree_left) <= 1 /\
                       0 <=
                         avl_insert_model_hgt (m1 new_left) -
                         avl_insert_model_hgt (m1 tree_left))
                      ==>
                      (-(&balancing) - 1 <=
                         avl_insert_model_hgt (m1 new_left) -
                         avl_insert_model_hgt (m1 tree_right) /\
                       avl_insert_model_hgt (m1 new_left) -
                         avl_insert_model_hgt (m1 tree_right) <=
                         &balancing + 1) /\
                      !result :
                        ('index, 'carrier) avl_insert_t2.
                        (avl_insert_model_seq (m1 result) =
                           node_model
                             (avl_insert_model_seq (m1 new_left))
                             tree_root
                             (avl_insert_model_seq (m1 tree_right)) /\
                         (let left_height =
                            avl_insert_model_hgt (m1 new_left) in
                          let right_height =
                            avl_insert_model_hgt (m1 tree_right) in
                          let expected_height =
                            1 +
                              (if left_height < right_height
                               then right_height
                               else left_height) in
                          let result_height =
                            avl_insert_model_hgt (m1 result) in
                            (0 <= expected_height - result_height /\
                             expected_height - result_height <= 1) /\
                            ((-(&balancing) <=
                                left_height - right_height /\
                              left_height - right_height <= &balancing)
                             ==>
                             expected_height = result_height)))
                        ==>
                        let extended_split =
                          avl_insert_right_extend
                            split tree_root
                            (avl_insert_model_seq (m1 tree_right))
                        in
                          avl_insert_model_seq (m1 result) =
                            node_model
                              (avl_insert_split_left extended_split)
                              d
                              (avl_insert_split_right extended_split) /\
                          (selected s extended_split /\
                           avl_insert_rebuild extended_split =
                             avl_insert_model_seq (m1 t3)) /\
                          avl_insert_model_hgt (m1 result) -
                            avl_insert_model_hgt (m1 t3) <= 1 /\
                          0 <=
                            avl_insert_model_hgt (m1 result) -
                            avl_insert_model_hgt (m1 t3)
                | AvlInsertRight right_selector =>
                    ((0 <= avl_insert_model_hgt (m1 t3) /\
                      avl_insert_model_hgt (m1 tree_right) <
                        avl_insert_model_hgt (m1 t3)) /\
                     selection_possible right_selector
                       (avl_insert_model_seq (m1 tree_right))) /\
                    !split
                      (new_right :
                        ('index, 'carrier) avl_insert_t2).
                      (avl_insert_model_seq (m1 new_right) =
                         node_model
                           (avl_insert_split_left split)
                           d
                           (avl_insert_split_right split) /\
                       (selected right_selector split /\
                        avl_insert_rebuild split =
                          avl_insert_model_seq (m1 tree_right)) /\
                       avl_insert_model_hgt (m1 new_right) -
                         avl_insert_model_hgt (m1 tree_right) <= 1 /\
                       0 <=
                         avl_insert_model_hgt (m1 new_right) -
                         avl_insert_model_hgt (m1 tree_right))
                      ==>
                      (-(&balancing) - 1 <=
                         avl_insert_model_hgt (m1 tree_left) -
                         avl_insert_model_hgt (m1 new_right) /\
                       avl_insert_model_hgt (m1 tree_left) -
                         avl_insert_model_hgt (m1 new_right) <=
                         &balancing + 1) /\
                      !result :
                        ('index, 'carrier) avl_insert_t2.
                        (avl_insert_model_seq (m1 result) =
                           node_model
                             (avl_insert_model_seq (m1 tree_left))
                             tree_root
                             (avl_insert_model_seq (m1 new_right)) /\
                         (let left_height =
                            avl_insert_model_hgt (m1 tree_left) in
                          let right_height =
                            avl_insert_model_hgt (m1 new_right) in
                          let expected_height =
                            1 +
                              (if left_height < right_height
                               then right_height
                               else left_height) in
                          let result_height =
                            avl_insert_model_hgt (m1 result) in
                            (0 <= expected_height - result_height /\
                             expected_height - result_height <= 1) /\
                            ((-(&balancing) <=
                                left_height - right_height /\
                              left_height - right_height <= &balancing)
                             ==>
                             expected_height = result_height)))
                        ==>
                        let extended_split =
                          avl_insert_left_extend
                            (avl_insert_model_seq (m1 tree_left))
                            tree_root split
                        in
                          avl_insert_model_seq (m1 result) =
                            node_model
                              (avl_insert_split_left extended_split)
                              d
                              (avl_insert_split_right extended_split) /\
                          (selected s extended_split /\
                           avl_insert_rebuild extended_split =
                             avl_insert_model_seq (m1 t3)) /\
                          avl_insert_model_hgt (m1 result) -
                            avl_insert_model_hgt (m1 t3) <= 1 /\
                          0 <=
                            avl_insert_model_hgt (m1 result) -
                            avl_insert_model_hgt (m1 t3)
                | AvlInsertHere =>
                    -(&balancing) <=
                      avl_insert_model_hgt (m1 tree_left) -
                      avl_insert_model_hgt (m1 tree_right) /\
                    avl_insert_model_hgt (m1 tree_left) -
                      avl_insert_model_hgt (m1 tree_right) <=
                      &balancing /\
                    !result :
                      ('index, 'carrier) avl_insert_t2.
                      (avl_insert_model_seq (m1 result) =
                         node_model
                           (avl_insert_model_seq (m1 tree_left))
                           d
                           (avl_insert_model_seq (m1 tree_right)) /\
                       avl_insert_model_hgt (m1 result) =
                         1 +
                           (if avl_insert_model_hgt (m1 tree_left) <
                               avl_insert_model_hgt (m1 tree_right)
                            then
                              avl_insert_model_hgt (m1 tree_right)
                            else
                              avl_insert_model_hgt (m1 tree_left)))
                      ==>
                      let root_split =
                        AvlInsertSplit
                          (avl_insert_model_seq (m1 tree_left))
                          (SOME tree_root)
                          (avl_insert_model_seq (m1 tree_right))
                      in
                        avl_insert_model_seq (m1 result) =
                          node_model
                            (avl_insert_split_left root_split)
                            d
                            (avl_insert_split_right root_split) /\
                        (selected s root_split /\
                         avl_insert_rebuild root_split =
                           avl_insert_model_seq (m1 t3)) /\
                        avl_insert_model_hgt (m1 result) -
                          avl_insert_model_hgt (m1 t3) <= 1 /\
                        0 <=
                          avl_insert_model_hgt (m1 result) -
                          avl_insert_model_hgt (m1 t3)))``;
