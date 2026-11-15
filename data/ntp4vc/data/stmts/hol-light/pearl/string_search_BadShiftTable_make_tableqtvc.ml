(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/string_search_BadShiftTable_make_tableqtvc: the verification
  condition for constructing a bad-character shift table over a byte string,
  including signed 63-bit bounds, an abstract map container with a finite-map
  view, loop invariants, and the final shift-table invariant. This file
  contains no proof.
*)

let bad_shift_table_output = open_out "/dev/null";;
let bad_shift_table_formatter =
  Format.formatter_of_out_channel bad_shift_table_output;;
let bad_shift_table_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file bad_shift_table_formatter path);;
let bad_shift_table_words_loaded =
  Toploop.use_file bad_shift_table_formatter "Library/words.ml";;
Hol_loader.file_loader := bad_shift_table_previous_loader;;
Format.pp_print_flush bad_shift_table_formatter ();;
close_out bad_shift_table_output;;
if not bad_shift_table_words_loaded
then failwith "failed to load Library/words.ml";;

let bad_shift_table_nat_of_int = new_definition
 `bad_shift_table_nat_of_int (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let bad_shift_table_nth = new_definition
 `bad_shift_table_nth (pat:byte list) (i:int) =
    if bad_shift_table_nat_of_int i < LENGTH pat
    then EL (bad_shift_table_nat_of_int i) pat
    else (word 0:byte)`;;

let bad_shift_table_mem = new_definition
 `bad_shift_table_mem
    (c:byte) (m:byte->((63)word)option) <=>
    ?v:(63)word. m c = SOME v`;;

let bad_shift_table_lookup = new_definition
 `bad_shift_table_lookup
    (m:byte->((63)word)option) (c:byte) =
    @v:(63)word. m c = SOME v`;;

let bad_shift_table_empty = new_definition
 `bad_shift_table_empty =
    (\c:byte. (NONE:((63)word)option))`;;

let bad_shift_table_update = new_definition
 `bad_shift_table_update
    (m:byte->((63)word)option) (c:byte) (v:(63)word) =
    (\d:byte. if d = c then SOME v else m d)`;;

let bad_shift_table_int63_in_bounds = new_definition
 `bad_shift_table_int63_in_bounds (x:int) <=>
    --(&2 pow 62) <= x /\ x <= &2 pow 62 - (&1:int)`;;

let bad_shift_table_prefix_invariant = new_definition
 `bad_shift_table_prefix_invariant
    (pat:byte list) (sht:byte->((63)word)option)
    (m:int) (bound:int) (upper:int) <=>
    (!j:int.
       (&0:int) <= j /\ j < bound
       ==> bad_shift_table_mem (bad_shift_table_nth pat j) sht) /\
    (!c:byte.
       bad_shift_table_mem c sht
       ==> (&1:int) <= ival (bad_shift_table_lookup sht c) /\
           ival (bad_shift_table_lookup sht c) <= upper) /\
    (!c:byte.
       bad_shift_table_mem c sht
       ==> !j:int.
             m - ival (bad_shift_table_lookup sht c) < j /\ j < bound
             ==> ~(bad_shift_table_nth pat j = c))`;;

let bad_shift_table_final_invariant = new_definition
 `bad_shift_table_final_invariant
    (pat:byte list) (sht:byte->((63)word)option) <=>
    (!j:int.
       (&0:int) <= j /\ j < (&(LENGTH pat):int)
       ==> bad_shift_table_mem (bad_shift_table_nth pat j) sht) /\
    (!c:byte.
       bad_shift_table_mem c sht
       ==> (&1:int) <= ival (bad_shift_table_lookup sht c) /\
           ival (bad_shift_table_lookup sht c) <=
             (&(LENGTH pat):int) + (&1:int)) /\
    (!c:byte.
       bad_shift_table_mem c sht
       ==> !j:int.
             (&1:int) <= j /\
             j < ival (bad_shift_table_lookup sht c)
             ==> ~(bad_shift_table_nth
                     pat ((&(LENGTH pat):int) - j) = c))`;;

let statement =
 `!to_fmap:A->byte->((63)word)option.
  !m:(63)word.
  !pat1:byte list.
  !sht1:A.
    ival m = (&(LENGTH pat1):int)
    ==> (&0:int) <= (&(LENGTH pat1):int)
    ==> to_fmap sht1 = bad_shift_table_empty
    ==> bad_shift_table_int63_in_bounds (ival m - (&1:int)) /\
        (!o1:(63)word.
           ival o1 = ival m - (&1:int)
           ==>
           (((&0:int) <= ival o1 + (&1:int)
             ==>
             bad_shift_table_prefix_invariant
               pat1 (to_fmap sht1) (ival m) (&0:int)
               (ival m + (&1:int)) /\
             (!sht2:A.
                (!i:(63)word.
                   let i1 = ival i in
                   ((&0:int) <= i1 /\ i1 <= ival o1) /\
                   bad_shift_table_prefix_invariant
                     pat1 (to_fmap sht2) (ival m) i1
                     (ival m + (&1:int))
                   ==>
                   bad_shift_table_int63_in_bounds (ival m - ival i) /\
                   (!o2:(63)word.
                      ival o2 = ival m - ival i
                      ==>
                      ((&0:int) <= ival i /\
                       ival i < (&(LENGTH pat1):int)) /\
                      (!sht3:A.
                         to_fmap sht3 =
                           bad_shift_table_update
                             (to_fmap sht2)
                             (bad_shift_table_nth pat1 (ival i)) o2
                         ==>
                         bad_shift_table_prefix_invariant
                           pat1 (to_fmap sht3) (ival m) (i1 + (&1:int))
                           (ival m + (&1:int))))) /\
                (bad_shift_table_prefix_invariant
                   pat1 (to_fmap sht2) (ival m) (ival o1 + (&1:int))
                   (ival m + (&1:int))
                 ==>
                 bad_shift_table_final_invariant pat1 (to_fmap sht2)))) /\
            (ival o1 + (&1:int) < (&0:int)
             ==> bad_shift_table_final_invariant pat1 (to_fmap sht1))))`;;
