(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/tables_MapBase_getqtvc: the sorted AVL sequence-map lookup
  verification condition relating a selected split to map membership,
  cardinality, and the returned element. This file contains no proof.
*)

let mapbase_get_tree_INDUCT,mapbase_get_tree_RECURSION = define_type
  "mapbase_get_tree =
       MapBaseGetEmpty
     | MapBaseGetNode mapbase_get_tree A mapbase_get_tree num C";;

let statement =
 `!balancing:num.
  !unit_value:C.
  !key:A->K.
  !le:K->K->bool.
  !seq_model:(A,C)mapbase_get_tree->A list.
  !real_height:(A,C)mapbase_get_tree->int.
  !balanced:(A,C)mapbase_get_tree->bool.
  !repr:B->(A,C)mapbase_get_tree.
  !m1:B->A list#int.
  !field:M->B.
  !make_func:A list->K->A.
  !domain_closure:A list->K->bool.
  !make_func_closure:A list->K->A.
  !t2:T2.
  !selector:S.
  !part:P.
  !t5:M.
  !k:K.
    let key_eq = \(x:K) (y:K). le x y /\ le y x in
    let key_lt = \(x:K) (y:K). le x y /\ ~le y x in
    let node_model =
      \(left:A list) (datum:A) (right:A list).
        APPEND left (CONS datum right) in
    let seq = \object:B. FST (m1 object) in
    let hgt = \object:B. SND (m1 object) in
    let split_left =
      \((left:A list),(middle:A option),(right:A list)). left in
    let split_middle =
      \((left:A list),(middle:A option),(right:A list)). middle in
    let split_right =
      \((left:A list),(middle:A option),(right:A list)). right in
    let option_to_seq =
      \middle:A option.
        if middle = NONE then []
        else [@datum. middle = SOME datum] in
    let rebuild =
      \parts:A list#A option#A list.
        APPEND
          (APPEND (split_left parts)
                  (option_to_seq (split_middle parts)))
          (split_right parts) in
    let selection_possible =
      \values:A list.
        !i j:int.
          (&0:int) <= i /\ i < j /\
          j < (&(LENGTH values):int)
          ==> key_lt
                (key (EL (num_of_int i) values))
                (key (EL (num_of_int j) values)) in
    let upper_bound =
      \(upper:K) (values:A list).
        !i:int.
          (&0:int) <= i /\ i < (&(LENGTH values):int)
          ==> key_lt (key (EL (num_of_int i) values)) upper in
    let lower_bound =
      \(lower:K) (values:A list).
        !i:int.
          (&0:int) <= i /\ i < (&(LENGTH values):int)
          ==> key_lt lower (key (EL (num_of_int i) values)) in
    let selected =
      \(selected_key:K) (parts:A list#A option#A list).
        upper_bound selected_key (split_left parts) /\
        lower_bound selected_key (split_right parts) /\
        (if split_middle parts = NONE then T
         else
           let datum = @datum. split_middle parts = SOME datum in
           key_eq selected_key (key datum)) in
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
    let result_matches_middle =
      \(result:A option) (parts:A list#A option#A list).
        if result = NONE
        then split_middle parts = NONE
        else split_middle parts = result in
    let result_conclusion =
      \(result:A option) (map:M) (sought_key:K).
        if result = NONE then
          ~(m3_domain map sought_key)
        else
          let datum = @datum. result = SOME datum in
          (&0:int) < m3_cardinality map /\
          key_eq (key datum) sought_key /\
          m3_domain map sought_key /\
          m3_function map sought_key = datum in
    let background =
      (0 < balancing /\
       (!x:C. x = unit_value /\ unit_value = x) /\
       (!x:K. le x x) /\
       (!x y z:K. le x y /\ le y z ==> le x z) /\
       (!x y:K. le x y \/ le y x) /\
       seq_model MapBaseGetEmpty = [] /\
       (!left_tree:(A,C)mapbase_get_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_get_tree.
        !height:num.
        !cached_unit:C.
          seq_model
            (MapBaseGetNode
              left_tree datum right_tree height cached_unit) =
          node_model
            (seq_model left_tree) datum (seq_model right_tree)) /\
       real_height MapBaseGetEmpty = (&0:int) /\
       (!left_tree:(A,C)mapbase_get_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_get_tree.
        !height:num.
        !cached_unit:C.
          real_height
            (MapBaseGetNode
              left_tree datum right_tree height cached_unit) =
          (&1:int) +
          (if real_height left_tree < real_height right_tree
           then real_height right_tree else real_height left_tree)) /\
       balanced MapBaseGetEmpty /\
       (!left_tree:(A,C)mapbase_get_tree.
        !datum:A.
        !right_tree:(A,C)mapbase_get_tree.
        !height:num.
        !cached_unit:C.
          (balanced
             (MapBaseGetNode
               left_tree datum right_tree height cached_unit) <=>
           (&height:int) =
             real_height
               (MapBaseGetNode
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
    let values = seq object in
    background
    ==>
    (selection_possible values /\
     (!parts:A list#A option#A list.
      !result:A option.
        ((selected k parts /\ rebuild parts = values) /\
         result_matches_middle result parts)
        ==> result_conclusion result t5 k))`;;
