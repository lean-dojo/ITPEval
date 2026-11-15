(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/tables_MapBase_joinqtvc: the sorted AVL sequence-map join
  verification condition preserving ordering around a pivot, side membership
  and values, pivot binding, cardinality, and bounded height loss. This file
  contains no proof.
*)

let mapbase_join_tree_INDUCT,mapbase_join_tree_RECURSION = define_type
  "mapbase_join_tree =
       MapBaseJoinEmpty
     | MapBaseJoinNode mapbase_join_tree A mapbase_join_tree num C";;

let statement =
 `!balancing:num.
  !unit_value:C.
  !key:A->K.
  !le:K->K->bool.
  !seq_model:(A,C)mapbase_join_tree->A list.
  !real_height:(A,C)mapbase_join_tree->int.
  !balanced:(A,C)mapbase_join_tree->bool.
  !repr:B->(A,C)mapbase_join_tree.
  !m1:B->A list#int.
  !field:M->B.
  !make_func:A list->K->A.
  !domain_closure:A list->K->bool.
  !make_func_closure:A list->K->A.
  !l r:M.
  !d:A.
    let key_eq = \(x:K) (y:K). le x y /\ le y x in
    let key_lt = \(x:K) (y:K). le x y /\ ~le y x in
    let node_model =
      \(left:A list) (datum:A) (right:A list).
        APPEND left (CONS datum right) in
    let seq = \object:B. FST (m1 object) in
    let hgt = \object:B. SND (m1 object) in
    let selection_possible =
      \values:A list.
        !i j:int.
          (&0:int) <= i /\ i < j /\
          j < (&(LENGTH values):int)
          ==> key_lt
                (key (EL (num_of_int i) values))
                (key (EL (num_of_int j) values)) in
    let domain =
      \(values:A list) (sought_key:K).
        ?i:int.
          ((&0:int) <= i /\ i < (&(LENGTH values):int)) /\
          key_eq (key (EL (num_of_int i) values)) sought_key in
    let m3_domain =
      \(map:M) (sought_key:K).
        domain_closure (seq (field map)) sought_key in
    let m3_function =
      \(map:M) (sought_key:K).
        make_func_closure (seq (field map)) sought_key in
    let m3_cardinality =
      \map:M. (&(LENGTH (seq (field map))):int) in
    let background =
      (0 < balancing /\
       (!x:C. x = unit_value /\ unit_value = x) /\
       (!x:K. le x x) /\
       (!x y z:K. le x y /\ le y z ==> le x z) /\
       (!x y:K. le x y \/ le y x) /\
       seq_model MapBaseJoinEmpty = [] /\
       (!left_tree:(A,C)mapbase_join_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_join_tree.
        !height:num.
        !cached_unit:C.
          seq_model
            (MapBaseJoinNode
              left_tree datum right_tree height cached_unit) =
          node_model
            (seq_model left_tree) datum (seq_model right_tree)) /\
       real_height MapBaseJoinEmpty = (&0:int) /\
       (!left_tree:(A,C)mapbase_join_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_join_tree.
        !height:num.
        !cached_unit:C.
          real_height
            (MapBaseJoinNode
              left_tree datum right_tree height cached_unit) =
          (&1:int) +
          (if real_height left_tree < real_height right_tree
           then real_height right_tree else real_height left_tree)) /\
       balanced MapBaseJoinEmpty /\
       (!left_tree:(A,C)mapbase_join_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_join_tree.
        !height:num.
        !cached_unit:C.
          (balanced
             (MapBaseJoinNode
               left_tree datum right_tree height cached_unit) <=>
           (&height:int) =
             real_height
               (MapBaseJoinNode
                 left_tree datum right_tree height cached_unit) /\
           cached_unit = unit_value /\
           (--(&balancing:int) <=
              real_height right_tree - real_height left_tree /\
            real_height right_tree - real_height left_tree <=
              (&balancing:int)) /\
           balanced left_tree /\ balanced right_tree)) /\
       (!object:B.
          balanced (repr object) /\
          seq object = seq_model (repr object) /\
          hgt object = real_height (repr object)) /\
       (!left right:B.
          repr left = repr right /\ m1 left = m1 right
          ==> left = right) /\
       (!map:M. selection_possible (seq (field map))) /\
       (!left right:M. field left = field right ==> left = right) /\
       (!values:A list.
        !sought_key:K.
        !i:int.
          selection_possible values /\
          domain values sought_key /\
          (&0:int) <= i /\
          i < (&(LENGTH values):int) /\
          key_eq (key (EL (num_of_int i) values)) sought_key
          ==> make_func values sought_key =
              EL (num_of_int i) values) /\
       (!values:A list.
        !sought_key:K.
          (domain_closure values sought_key <=>
           domain values sought_key)) /\
       (!values:A list.
        !sought_key:K.
          make_func_closure values sought_key =
          make_func values sought_key)) in
    let o1 = field r in
    let o2 = field l in
    background
    ==> (!k:K. m3_domain l k ==> key_lt k (key d))
    ==> (!k:K. m3_domain r k ==> key_lt (key d) k)
    ==> (!o3:B.
          seq o3 =
            node_model (seq o2) d (seq o1) /\
          (let hl = hgt o2 in
           let hr = hgt o1 in
           let expected_height =
             (&1:int) + (if hl < hr then hr else hl) in
           let result_height = hgt o3 in
             (&0:int) <= expected_height - result_height /\
             expected_height - result_height <= (&1:int))
          ==> selection_possible (seq o3) /\
              (!result:M.
                 field result = o3
                 ==> (!k:K.
                        key_lt k (key d)
                        ==> (m3_domain result k <=>
                             m3_domain l k)) /\
                     (!k:K.
                        key_lt k (key d) /\ m3_domain result k
                        ==> m3_function result k =
                            m3_function l k) /\
                     (!k:K.
                        key_lt (key d) k
                        ==> (m3_domain result k <=>
                             m3_domain r k)) /\
                     (!k:K.
                        key_lt (key d) k /\ m3_domain result k
                        ==> m3_function result k =
                            m3_function r k) /\
                     (!k:K.
                        key_eq k (key d)
                        ==> m3_domain result k /\
                            m3_function result k = d) /\
                     m3_cardinality result =
                       (&1:int) +
                       m3_cardinality l +
                       m3_cardinality r))`;;
