(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/incremental_Ce_interesting_dummy_updateqtvc: a signed 32-bit
  dummy-update verification condition requiring 42 and its exact-integer
  double to remain in signed 32-bit bounds, and constraining any second
  output equal to that double to be at most 42. This file contains no proof.
*)

let incremental_interesting_output = open_out "/dev/null";;
let incremental_interesting_formatter =
  Format.formatter_of_out_channel incremental_interesting_output;;
let incremental_interesting_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file incremental_interesting_formatter path);;
let incremental_interesting_words_loaded =
  Toploop.use_file incremental_interesting_formatter "Library/words.ml";;
Hol_loader.file_loader := incremental_interesting_previous_loader;;
Format.pp_print_flush incremental_interesting_formatter ();;
close_out incremental_interesting_output;;
if not incremental_interesting_words_loaded then
  failwith "failed to load Library/words.ml";;

let statement =
  `!r:int32.
     (&22:int) < ival r
     ==>
     (--(&2147483648:int) <= (&42:int) /\
      (&42:int) <= (&2147483647:int)) /\
     (!o1:int32.
        ival o1 = (&42:int)
        ==>
        (--(&2147483648:int) <= ival o1 + ival o1 /\
         ival o1 + ival o1 <= (&2147483647:int)) /\
        (!o2:int32.
           ival o2 = ival o1 + ival o1
           ==> ival o2 <= (&42:int)))`;;
