(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/tables_MapBase_viewqtvc: the sorted AVL sequence-map view
  verification condition relating an empty-or-node tree view to map
  cardinality, height, membership, and stored values. This file contains no
  proof.
*)

let mapbase_view_tree_INDUCT,mapbase_view_tree_RECURSION = define_type
  "mapbase_view_tree =
       MapBaseViewTreeEmpty
     | MapBaseViewTreeNode mapbase_view_tree A mapbase_view_tree num C";;

let statement =
 `!balancing:num.
  !unit_value:C.
  !key:A->K.
  !le:K->K->bool.
  !seq_model:(A,C)mapbase_view_tree->A list.
  !real_height:(A,C)mapbase_view_tree->int.
  !balanced:(A,C)mapbase_view_tree->bool.
  !repr:B->(A,C)mapbase_view_tree.
  !m1:B->A list#int.
  !field:M->B.
  !make_func:A list->K->A.
  !domain_closure:A list->K->bool.
  !make_func_closure:A list->K->A.
  !t2:T2.
  !selector:S.
  !part:P.
  !t5:M.
    let key_eq = \(x:K) (y:K). le x y /\ le y x in
    let key_lt = \(x:K) (y:K). le x y /\ ~le y x in
    let node_model =
      \(left:A list) (datum:A) (right:A list).
        APPEND left (CONS datum right) in
    let seq = \object:B. FST (m1 object) in
    let hgt = \object:B. SND (m1 object) in
    let input_payload =
      \view:(B#A#B#num#C)option. @payload. view = SOME payload in
    let input_left =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        left in
    let input_datum =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        datum in
    let input_right =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        right in
    let input_height =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        height in
    let input_summary =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        summary in
    let result_payload =
      \view:(M#A#M#num)option. @payload. view = SOME payload in
    let result_left =
      \((left:M),(datum:A),(right:M),(height:num)). left in
    let result_datum =
      \((left:M),(datum:A),(right:M),(height:num)). datum in
    let result_right =
      \((left:M),(datum:A),(right:M),(height:num)). right in
    let result_height =
      \((left:M),(datum:A),(right:M),(height:num)). height in
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
    let input_fact =
      \(object:B) (view:(B#A#B#num#C)option).
        if view = NONE then
          hgt object = (&0:int) /\ seq object = []
        else
          let payload = input_payload view in
          let left = input_left payload in
          let datum = input_datum payload in
          let right = input_right payload in
          let height = input_height payload in
          let summary = input_summary payload in
          seq object = node_model (seq left) datum (seq right) /\
          summary = unit_value /\
          (let hl = hgt left in
           let hr = hgt right in
             --(&balancing:int) <= hl - hr /\
             hl - hr <= (&balancing:int) /\
             hgt object = (&height:int) /\
             (&height:int) =
               (&1:int) + (if hl < hr then hr else hl)) in
    let view_side_condition =
      \view:(B#A#B#num#C)option.
        if view = NONE then T
        else
          let payload = input_payload view in
          let left = input_left payload in
          let right = input_right payload in
          selection_possible (seq right) /\
          (!right_map:M.
             field right_map = right
             ==> selection_possible (seq left)) in
    let result_matches =
      \(view:(B#A#B#num#C)option)
       (result:(M#A#M#num)option).
        if view = NONE then
          result = NONE
        else
          let payload = input_payload view in
          ?right_map:M.
            field right_map = input_right payload /\
            ?left_map:M.
              field left_map = input_left payload /\
              result =
                SOME
                  (left_map,input_datum payload,right_map,
                   input_height payload) in
    let result_conclusion =
      \result:(M#A#M#num)option.
        if result = NONE then
          m3_cardinality t5 = (&0:int) /\
          (!sought_key:K. ~(m3_domain t5 sought_key))
        else
          let payload = result_payload result in
          let left_map = result_left payload in
          let datum = result_datum payload in
          let right_map = result_right payload in
          let height = result_height payload in
          m3_cardinality t5 =
            (&1:int) +
            m3_cardinality left_map +
            m3_cardinality right_map /\
          (&height:int) = hgt (field t5) /\
          (let pivot = key datum in
           (!sought_key:K.
              key_lt sought_key pivot
              ==> (m3_domain left_map sought_key <=>
                   m3_domain t5 sought_key)) /\
           (!sought_key:K.
              key_lt sought_key pivot /\
              m3_domain left_map sought_key
              ==> m3_function left_map sought_key =
                  m3_function t5 sought_key) /\
           (!sought_key:K.
              le pivot sought_key
              ==> ~(m3_domain left_map sought_key)) /\
           (!sought_key:K.
              key_lt pivot sought_key
              ==> (m3_domain right_map sought_key <=>
                   m3_domain t5 sought_key)) /\
           (!sought_key:K.
              key_lt pivot sought_key /\
              m3_domain right_map sought_key
              ==> m3_function right_map sought_key =
                  m3_function t5 sought_key) /\
           (!sought_key:K.
              le sought_key pivot
              ==> ~(m3_domain right_map sought_key)) /\
           (!sought_key:K.
              key_eq sought_key pivot
              ==> m3_domain t5 sought_key /\
                  m3_function t5 sought_key = datum) /\
           m3_domain t5 pivot /\
           m3_function t5 pivot = datum) in
    let background =
      (0 < balancing /\
       (!x:C. x = unit_value /\ unit_value = x) /\
       (!x:K. le x x) /\
       (!x y z:K. le x y /\ le y z ==> le x z) /\
       (!x y:K. le x y \/ le y x) /\
       seq_model MapBaseViewTreeEmpty = [] /\
       (!left_tree:(A,C)mapbase_view_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_view_tree.
        !height:num.
        !cached_unit:C.
          seq_model
            (MapBaseViewTreeNode
              left_tree datum right_tree height cached_unit) =
          node_model
            (seq_model left_tree) datum (seq_model right_tree)) /\
       real_height MapBaseViewTreeEmpty = (&0:int) /\
       (!left_tree:(A,C)mapbase_view_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_view_tree.
        !height:num.
        !cached_unit:C.
          real_height
            (MapBaseViewTreeNode
              left_tree datum right_tree height cached_unit) =
          (&1:int) +
          (if real_height left_tree < real_height right_tree
           then real_height right_tree else real_height left_tree)) /\
       balanced MapBaseViewTreeEmpty /\
       (!left_tree:(A,C)mapbase_view_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_view_tree.
        !height:num.
        !cached_unit:C.
          (balanced
             (MapBaseViewTreeNode
               left_tree datum right_tree height cached_unit) <=>
           (&height:int) =
             real_height
               (MapBaseViewTreeNode
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
    let object = field t5 in
    background
    ==>
    (!view:(B#A#B#num#C)option.
       input_fact object view
       ==>
       view_side_condition view /\
       (!result:(M#A#M#num)option.
          result_matches view result
          ==> result_conclusion result))`;;
