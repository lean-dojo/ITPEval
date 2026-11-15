(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/string_search_BadShiftTable_searchqtvc: the verification condition
  for bad-character-shift string search over byte strings, preserving the
  shift-table invariant, signed 63-bit bounds, skipped-position exclusion,
  loop progress, and the final search specification. This file contains no
  proof.
*)

let string_search_output = open_out "/dev/null";;
let string_search_formatter =
  Format.formatter_of_out_channel string_search_output;;
let string_search_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file string_search_formatter path);;
let string_search_words_loaded =
  Toploop.use_file string_search_formatter "Library/words.ml";;
Hol_loader.file_loader := string_search_previous_loader;;
Format.pp_print_flush string_search_formatter ();;
close_out string_search_output;;
if not string_search_words_loaded
then failwith "failed to load Library/words.ml";;

ignore (new_definition
 `string_search_nat_of_int (i:int) =
    if i < (&0:int) then 0 else num_of_int i`);;

ignore (new_definition
 `string_search_nth (s:byte list) (i:int) =
    if string_search_nat_of_int i < LENGTH s
    then EL (string_search_nat_of_int i) s
    else (word 0:byte)`);;

ignore (new_definition
 `string_search_substring_eq
    (s:byte list) (p:int) (n:int) (out:byte list) <=>
    LENGTH out = string_search_nat_of_int n /\
    (!k:num.
       k < LENGTH out
       ==> EL k out = string_search_nth s (p + (&k:int)))`);;

ignore (new_definition
 `string_search_matches (pat:byte list) (text:byte list) (p:int) <=>
    (&0:int) <= p /\
    p <= (&(LENGTH text):int) - (&(LENGTH pat):int) /\
    string_search_substring_eq
      text p (&(LENGTH pat):int) pat`);;

ignore (new_definition
 `string_search_map_mem
    (c:byte) (sht:byte->((63)word)option) <=>
    ?v:(63)word. sht c = SOME v`);;

ignore (new_definition
 `string_search_map_lookup
    (sht:byte->((63)word)option) (c:byte) =
    @v:(63)word. sht c = SOME v`);;

ignore (new_definition
 `string_search_int63_in_bounds (x:int) <=>
    --(&2 pow 62) <= x /\ x <= &2 pow 62 - (&1:int)`);;

ignore (new_definition
 `string_search_shift_table_invariant
    (pat:byte list) (sht:byte->((63)word)option) <=>
    (!j:int. !c:byte.
       (&0:int) <= j /\ j < (&(LENGTH pat):int)
       ==> c = string_search_nth pat j
       ==> string_search_map_mem c sht) /\
    (!c:byte.
       string_search_map_mem c sht
       ==> (&1:int) <= ival (string_search_map_lookup sht c) /\
           ival (string_search_map_lookup sht c) <=
             (&(LENGTH pat):int) + (&1:int)) /\
    (!c:byte.
       string_search_map_mem c sht
       ==> !j:int.
             (&1:int) <= j /\
             j < ival (string_search_map_lookup sht c)
             ==> ~(string_search_nth
                     pat ((&(LENGTH pat):int) - j) = c))`);;

let statement =
 `!pat text:byte list.
  !sht:byte->((63)word)option.
    string_search_shift_table_invariant pat sht
    ==>
    LENGTH pat <= LENGTH text
    ==>
    !m:(63)word.
      ival m = (&(LENGTH pat):int) /\
      (&0:int) <= (&(LENGTH pat):int)
      ==>
      !n:(63)word.
        ival n = (&(LENGTH text):int) /\
        (&0:int) <= (&(LENGTH text):int)
        ==>
        (((&0:int) <= (&0:int) /\ (&0:int) <= ival n) /\
         (!j:int.
            (&0:int) <= j /\ j < (&0:int)
            ==> j <= ival n - ival m
            ==> ~string_search_substring_eq text j (ival m) pat)) /\
        (!i:(63)word.
           (((&0:int) <= ival i /\ ival i <= ival n) /\
            (!j:int.
               (&0:int) <= j /\ j < ival i
               ==> j <= ival n - ival m
               ==> ~string_search_substring_eq text j (ival m) pat))
           ==>
           string_search_int63_in_bounds (ival n - ival m) /\
           (!o1:(63)word.
              ival o1 = ival n - ival m
              ==>
              if ival i <= ival o1 then
                ((&0:int) <= ival i /\
                 ival i <=
                   (&(LENGTH text):int) - (&(LENGTH pat):int)) /\
                (if string_search_matches pat text (ival i) then
                   (--(&1:int) <= ival i /\
                    ival i <=
                      (&(LENGTH text):int) - (&(LENGTH pat):int)) /\
                   (if ival i = --(&1:int) then
                      !j:int. ~string_search_matches pat text j
                    else
                      string_search_matches pat text (ival i))
                 else
                   string_search_int63_in_bounds (ival n - ival m) /\
                   (!o2:(63)word.
                      ival o2 = ival n - ival m
                      ==>
                      (ival i = ival o2 ==> i = o2)
                      ==>
                      if i = o2 then
                        (--(&1:int) <= --(&1:int) /\
                         --(&1:int) <=
                           (&(LENGTH text):int) -
                           (&(LENGTH pat):int)) /\
                        (!j:int. ~string_search_matches pat text j)
                      else
                        string_search_int63_in_bounds
                          (ival i + ival m) /\
                        (!o3:(63)word.
                           ival o3 = ival i + ival m
                           ==>
                           ((&0:int) <= ival o3 /\
                            ival o3 < (&(LENGTH text):int)) /\
                           (let c = string_search_nth text (ival o3) in
                            (if string_search_map_mem c sht then
                               string_search_map_mem c sht
                             else
                               string_search_int63_in_bounds
                                 (ival m + (&1:int))) /\
                            (!o4:(63)word.
                               (if string_search_map_mem c sht then
                                  o4 = string_search_map_lookup sht c /\
                                  o4 = string_search_map_lookup sht c
                                else
                                  ival o4 = ival m + (&1:int))
                               ==>
                               string_search_int63_in_bounds
                                 (ival i + ival o4) /\
                               (!o5:(63)word.
                                  ival o5 = ival i + ival o4
                                  ==>
                                  ((&0:int) <=
                                     ival n - ival m - ival i /\
                                   ival n - ival m - ival o5 <
                                     ival n - ival m - ival i) /\
                                  ((&0:int) <= ival o5 /\
                                   ival o5 <= ival n) /\
                                  (!j:int.
                                     (&0:int) <= j /\ j < ival o5
                                     ==> j <= ival n - ival m
                                     ==> ~string_search_substring_eq
                                           text j (ival m) pat)))))))
              else
                (--(&1:int) <= --(&1:int) /\
                 --(&1:int) <=
                   (&(LENGTH text):int) - (&(LENGTH pat):int)) /\
                (!j:int. ~string_search_matches pat text j)))`;;
