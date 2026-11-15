(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/incremental_Ce_int32_dummy_updateqtvc: a signed 32-bit dummy-update
  verification condition constraining the first output to 42 and the second
  output to its exact-integer double, then requiring it to equal 42. This file
  contains no proof.
*)

let incremental_output = open_out "/dev/null";;
let incremental_formatter =
  Format.formatter_of_out_channel incremental_output;;
let incremental_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file incremental_formatter path);;
let incremental_words_loaded =
  Toploop.use_file incremental_formatter "Library/words.ml";;
Hol_loader.file_loader := incremental_previous_loader;;
Format.pp_print_flush incremental_formatter ();;
close_out incremental_output;;
if not incremental_words_loaded then
  failwith "failed to load Library/words.ml";;

let statement =
  `!r:int32.
     ival r = (&22:int)
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
           ==> ival o2 = (&42:int)))`;;
