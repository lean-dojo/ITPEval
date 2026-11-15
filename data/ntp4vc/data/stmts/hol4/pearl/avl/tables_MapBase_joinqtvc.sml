(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/tables_MapBase_joinqtvc: the sorted sequence-map join
  verification condition preserving selection order, membership, stored
  values, and combined cardinality. This file contains no proof.

  The singleton function fields retain the source type index: for every index
  type, ('index -> unit) has exactly one extensional value. The element,
  tree-object, and map-object datatypes are therefore bijective indexed
  wrappers of arbitrary underlying carriers for the quantified source type
  instance.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  mapbase_element = MapBaseElement ('index -> unit) 'node
End

Datatype:
  mapbase_tree =
    MapBaseEmpty
  | MapBaseNode mapbase_tree
      (('index, 'node) mapbase_element)
      mapbase_tree num unit
End

Datatype:
  mapbase_model =
    MapBaseModel ((('index, 'node) mapbase_element) list) int
End

Datatype:
  mapbase_tree_object =
    MapBaseTreeObject ('index -> unit) 'tree_carrier
End

Datatype:
  mapbase_map_object =
    MapBaseMapObject ('index -> unit) 'map_carrier
End

Datatype:
  mapbase_summary =
    MapBaseSummary ('key -> bool)
      ('key -> (('index, 'node) mapbase_element)) int
End

val mapbase_model_seq_def = Define `
  mapbase_model_seq (MapBaseModel elements height) = elements`;

val mapbase_model_hgt_def = Define `
  mapbase_model_hgt (MapBaseModel elements height) = height`;

val mapbase_summary_domn_def = Define `
  mapbase_summary_domn (MapBaseSummary domn func card) = domn`;

val mapbase_summary_func_def = Define `
  mapbase_summary_func (MapBaseSummary domn func card) = func`;

val mapbase_summary_card_def = Define `
  mapbase_summary_card (MapBaseSummary domn func card) = card`;

val mapbase_int_to_num_def = Define `
  mapbase_int_to_num (z : int) = if z < 0 then 0 else Num z`;

val mapbase_key_eq_def = Define `
  mapbase_key_eq (le : 'key -> 'key -> bool) x y <=>
    le x y /\ le y x`;

val mapbase_key_lt_def = Define `
  mapbase_key_lt (le : 'key -> 'key -> bool) x y <=>
    le x y /\ ~le y x`;

val mapbase_selection_possible_def = Define `
  mapbase_selection_possible
      (key : 'element -> 'key)
      (le : 'key -> 'key -> bool)
      (ignored : 'selector)
      (elements : 'element list) <=>
    !i j : int.
      0 <= i /\ i < j /\ j < &(LENGTH elements) ==>
      mapbase_key_lt le
        (key (EL (mapbase_int_to_num i) elements))
        (key (EL (mapbase_int_to_num j) elements))`;

val mapbase_seq_model_def = Define `
  (mapbase_seq_model MapBaseEmpty = []) /\
  (mapbase_seq_model
      (MapBaseNode left root right height summary) =
     APPEND (mapbase_seq_model left)
       (root :: mapbase_seq_model right))`;

val mapbase_real_height_def = Define `
  (mapbase_real_height MapBaseEmpty = (0 : int)) /\
  (mapbase_real_height
      (MapBaseNode left root right height summary) =
     1 +
       (if mapbase_real_height left < mapbase_real_height right
        then mapbase_real_height right
        else mapbase_real_height left))`;

val mapbase_balanced_def = Define `
  (mapbase_balanced balancing MapBaseEmpty = T) /\
  (mapbase_balanced balancing
      (MapBaseNode left root right height summary) =
     (&height =
        mapbase_real_height
          (MapBaseNode left root right height summary) /\
      summary = () /\
      -(&balancing) <=
        mapbase_real_height right - mapbase_real_height left /\
      mapbase_real_height right - mapbase_real_height left <=
        &balancing /\
      mapbase_balanced balancing left /\
      mapbase_balanced balancing right))`;

val mapbase_domain_def = Define `
  mapbase_domain
      (key : 'element -> 'key)
      (le : 'key -> 'key -> bool)
      (elements : 'element list) sought <=>
    ?i : int.
      (0 <= i /\ i < &(LENGTH elements)) /\
      mapbase_key_eq le
        (key (EL (mapbase_int_to_num i) elements))
        sought`;

val mapbase_m3_def = Define `
  mapbase_m3 domain_closure make_func_closure m1 field object =
    let elements = mapbase_model_seq (m1 (field object))
    in
      MapBaseSummary
        (domain_closure elements)
        (make_func_closure elements)
        (&(LENGTH elements))`;

val tables_MapBase_join_vc =
  ``!(balancing : num)
      (key : (('index, 'node) mapbase_element) -> 'key)
      (le : 'key -> 'key -> bool)
      (repr :
        (('index, 'tree_carrier) mapbase_tree_object) ->
        ('index, 'node) mapbase_tree)
      (m1 :
        (('index, 'tree_carrier) mapbase_tree_object) ->
        ('index, 'node) mapbase_model)
      (field :
        (('index, 'map_carrier) mapbase_map_object) ->
        (('index, 'tree_carrier) mapbase_tree_object))
      (make_func :
        (('index, 'node) mapbase_element) list ->
        'key -> (('index, 'node) mapbase_element))
      (domain_closure :
        (('index, 'node) mapbase_element) list ->
        'key -> bool)
      (make_func_closure :
        (('index, 'node) mapbase_element) list ->
        'key -> (('index, 'node) mapbase_element))
      (l : ('index, 'map_carrier) mapbase_map_object)
      (d : ('index, 'node) mapbase_element)
      (r : ('index, 'map_carrier) mapbase_map_object).
      (0 : int) < &balancing ==>
      (!x. le x x) ==>
      (!x y z. le x y /\ le y z ==> le x z) ==>
      (!x y. le x y \/ le y x) ==>
      (!self.
         mapbase_balanced balancing (repr self) /\
         mapbase_model_seq (m1 self) =
           mapbase_seq_model (repr self) /\
         mapbase_model_hgt (m1 self) =
           mapbase_real_height (repr self)) ==>
      (!a b.
         repr a = repr b /\ m1 a = m1 b ==> a = b) ==>
      (!self.
         mapbase_selection_possible key le ()
           (mapbase_model_seq (m1 (field self)))) ==>
      (!a b. field a = field b ==> a = b) ==>
      (!elements sought i.
         mapbase_selection_possible key le () elements /\
         mapbase_domain key le elements sought /\
         0 <= i /\ i < &(LENGTH elements) /\
         mapbase_key_eq le
           (key (EL (mapbase_int_to_num i) elements))
           sought ==>
         make_func elements sought =
           EL (mapbase_int_to_num i) elements) ==>
      (!elements sought.
         domain_closure elements sought <=>
           mapbase_domain key le elements sought) ==>
      (!elements sought.
         make_func_closure elements sought =
           make_func elements sought) ==>
      (!k.
         mapbase_summary_domn
           (mapbase_m3 domain_closure make_func_closure
             m1 field l) k ==>
         mapbase_key_lt le k (key d)) ==>
      (!k.
         mapbase_summary_domn
           (mapbase_m3 domain_closure make_func_closure
             m1 field r) k ==>
         mapbase_key_lt le (key d) k) ==>
      let right_tree = field r in
      let left_tree = field l in
        !joined_tree :
          (('index, 'tree_carrier) mapbase_tree_object).
          (mapbase_model_seq (m1 joined_tree) =
             APPEND
               (mapbase_model_seq (m1 left_tree))
               (d :: mapbase_model_seq (m1 right_tree)) /\
           (let left_height = mapbase_model_hgt (m1 left_tree) in
            let right_height = mapbase_model_hgt (m1 right_tree) in
            let expected_height =
              1 +
                (if left_height < right_height
                 then right_height
                 else left_height) in
            let result_height = mapbase_model_hgt (m1 joined_tree)
            in
              (0 : int) <= expected_height - result_height /\
              expected_height - result_height <= 1))
          ==>
          mapbase_selection_possible key le ()
            (mapbase_model_seq (m1 joined_tree)) /\
          !result : ('index, 'map_carrier) mapbase_map_object.
            field result = joined_tree ==>
            (!k.
               mapbase_key_lt le k (key d) ==>
               (mapbase_summary_domn
                  (mapbase_m3 domain_closure make_func_closure
                    m1 field result) k <=>
                mapbase_summary_domn
                  (mapbase_m3 domain_closure make_func_closure
                    m1 field l) k)) /\
            (!k.
               mapbase_key_lt le k (key d) /\
               mapbase_summary_domn
                 (mapbase_m3 domain_closure make_func_closure
                   m1 field result) k ==>
               mapbase_summary_func
                 (mapbase_m3 domain_closure make_func_closure
                   m1 field result) k =
               mapbase_summary_func
                 (mapbase_m3 domain_closure make_func_closure
                   m1 field l) k) /\
            (!k.
               mapbase_key_lt le (key d) k ==>
               (mapbase_summary_domn
                  (mapbase_m3 domain_closure make_func_closure
                    m1 field result) k <=>
                mapbase_summary_domn
                  (mapbase_m3 domain_closure make_func_closure
                    m1 field r) k)) /\
            (!k.
               mapbase_key_lt le (key d) k /\
               mapbase_summary_domn
                 (mapbase_m3 domain_closure make_func_closure
                   m1 field result) k ==>
               mapbase_summary_func
                 (mapbase_m3 domain_closure make_func_closure
                   m1 field result) k =
               mapbase_summary_func
                 (mapbase_m3 domain_closure make_func_closure
                   m1 field r) k) /\
            (!k.
               mapbase_key_eq le k (key d) ==>
               mapbase_summary_domn
                 (mapbase_m3 domain_closure make_func_closure
                   m1 field result) k /\
               mapbase_summary_func
                 (mapbase_m3 domain_closure make_func_closure
                   m1 field result) k = d) /\
            mapbase_summary_card
                (mapbase_m3 domain_closure make_func_closure
                  m1 field result) =
              1 +
                mapbase_summary_card
                  (mapbase_m3 domain_closure make_func_closure
                    m1 field l) +
                mapbase_summary_card
                  (mapbase_m3 domain_closure make_func_closure
                    m1 field r)``;
