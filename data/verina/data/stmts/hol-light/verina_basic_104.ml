(*
  Statement-only formalization of VERINA corpus artifact verina_basic_104,
  catalog title "update_map": an executable association-list map update gives
  the second integer map priority, sorts the resulting entries by key, and is
  connected to its complete lookup correctness contract. This file contains
  no proof.
*)

let update_map_key_member =
  new_recursive_definition list_RECURSION
    `(!key:int.
        update_map_key_member key ([]:(int#int)list) <=> F) /\
     (!entry:int#int. !rest:(int#int)list. !key:int.
        update_map_key_member key (CONS entry rest) <=>
        key = FST entry \/ update_map_key_member key rest)`;;

let update_map_nodup_keys =
  new_recursive_definition list_RECURSION
    `(update_map_nodup_keys ([]:(int#int)list) <=> T) /\
     (!entry:int#int. !rest:(int#int)list.
        update_map_nodup_keys (CONS entry rest) <=>
        ~(update_map_key_member (FST entry) rest) /\
        update_map_nodup_keys rest)`;;

let update_map_empty = new_definition
  `update_map_empty:(int#int)list = []`;;

let update_map_insert = new_definition
  `update_map_insert
      (entries:(int#int)list) (key:int) (value:int) =
     APPEND
       (FILTER (\entry:int#int. ~(FST entry = key)) entries)
       (CONS (key,value) [])`;;

let update_map_precond = new_definition
  `update_map_precond
      (m1:(int#int)list) (m2:(int#int)list) <=>
     update_map_nodup_keys m1 /\
     update_map_nodup_keys m2`;;

let update_map_fold_inserts =
  new_recursive_definition list_RECURSION
    `(!acc:(int#int)list.
        update_map_fold_inserts ([]:(int#int)list) acc = acc) /\
     (!entry:int#int. !rest:(int#int)list.
      !acc:(int#int)list.
        update_map_fold_inserts (CONS entry rest) acc =
        update_map_fold_inserts rest
          (update_map_insert acc (FST entry) (SND entry)))`;;

let update_map_insert_sorted =
  new_recursive_definition list_RECURSION
    `(!entry:int#int.
        update_map_insert_sorted entry ([]:(int#int)list) =
        CONS entry []) /\
     (!current:int#int. !rest:(int#int)list. !entry:int#int.
        update_map_insert_sorted entry (CONS current rest) =
        if FST entry <= FST current then
          CONS entry (CONS current rest)
        else
          CONS current (update_map_insert_sorted entry rest))`;;

let update_map_sort_entries =
  new_recursive_definition list_RECURSION
    `(update_map_sort_entries ([]:(int#int)list) = []) /\
     (!entry:int#int. !rest:(int#int)list.
        update_map_sort_entries (CONS entry rest) =
        update_map_insert_sorted
          entry (update_map_sort_entries rest))`;;

let update_map = new_definition
  `update_map (m1:(int#int)list) (m2:(int#int)list) =
     let updated = update_map_fold_inserts m2 m1 in
     update_map_sort_entries updated`;;

let update_map_find =
  new_recursive_definition list_RECURSION
    `(!key:int.
        update_map_find ([]:(int#int)list) key =
        (NONE:int option)) /\
     (!entry:int#int. !rest:(int#int)list. !key:int.
        update_map_find (CONS entry rest) key =
        if FST entry = key then SOME (SND entry)
        else update_map_find rest key)`;;

let update_map_option_value =
  new_recursive_definition option_RECURSION
    `(update_map_option_value (NONE:int option) = &0) /\
     (!value:int.
        update_map_option_value (SOME value) = value)`;;

let update_map_m1_entry_condition = new_definition
  `update_map_m1_entry_condition
      (m2:(int#int)list) (result:(int#int)list)
      (entry:int#int) <=>
     if update_map_find m2 (FST entry) = NONE then
       update_map_find result (FST entry) = SOME (SND entry)
     else T`;;

let update_map_result_entry_condition = new_definition
  `update_map_result_entry_condition
      (m1:(int#int)list) (m2:(int#int)list)
      (entry:int#int) <=>
     let from_m1 = update_map_find m1 (FST entry) in
     let from_m2 = update_map_find m2 (FST entry) in
     if from_m1 = NONE then
       from_m2 = SOME (SND entry)
     else if from_m2 = NONE then
       SND entry = update_map_option_value from_m1
     else
       SND entry = update_map_option_value from_m2`;;

let update_map_postcond = new_definition
  `update_map_postcond
      (m1:(int#int)list) (m2:(int#int)list)
      (result:(int#int)list) <=>
     PAIRWISE
       (\first second:int#int. FST first <= FST second)
       result /\
     ALL
       (\entry:int#int.
          update_map_find result (FST entry) =
          SOME (SND entry))
       m2 /\
     ALL
       (update_map_m1_entry_condition m2 result)
       m1 /\
     ALL
       (update_map_result_entry_condition m1 m2)
       result`;;

let update_map_spec_satisfied =
  `!m1:(int#int)list. !m2:(int#int)list.
     update_map_precond m1 m2
     ==> update_map_postcond
           m1 m2 (update_map m1 m2)`;;
