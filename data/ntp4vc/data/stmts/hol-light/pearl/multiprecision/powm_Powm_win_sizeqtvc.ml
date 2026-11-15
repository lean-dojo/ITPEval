(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_win_sizeqtvc: the verification condition for
  selecting a modular-exponentiation window size from a signed 32-bit exponent
  bit count by a fixed threshold ladder. This file contains no proof.
*)

let powm_win_size_output = open_out "/dev/null";;
let powm_win_size_formatter =
  Format.formatter_of_out_channel powm_win_size_output;;
let powm_win_size_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file powm_win_size_formatter path);;
let powm_win_size_words_loaded =
  Toploop.use_file powm_win_size_formatter "Library/words.ml";;
Hol_loader.file_loader := powm_win_size_previous_loader;;
Format.pp_print_flush powm_win_size_formatter ();;
close_out powm_win_size_output;;
if not powm_win_size_words_loaded then
  failwith "failed to load Library/words.ml";;

let statement =
  `!eb:int32. !o1:bool. !result:int32.
     (ival eb = ival (word 0:int32) ==> o1 = T) /\
     (o1 = T ==> eb = (word 0:int32)) /\
     (if o1 = T then
        result = (word 0:int32)
      else if ival eb <= (&7:int) then
        result = (word 1:int32)
      else if ival eb <= (&25:int) then
        result = (word 2:int32)
      else if ival eb <= (&81:int) then
        result = (word 3:int32)
      else if ival eb <= (&214:int) then
        result = (word 4:int32)
      else if ival eb <= (&673:int) then
        result = (word 5:int32)
      else if ival eb <= (&1793:int) then
        result = (word 6:int32)
      else if ival eb <= (&4609:int) then
        result = (word 7:int32)
      else if ival eb <= (&11521:int) then
        result = (word 8:int32)
      else if ival eb <= (&28161:int) then
        result = (word 9:int32)
      else
        result = (word 10:int32))
     ==>
     (&0:int) <= ival result /\
     ival result <= (&10:int) /\
     ((&0:int) < ival eb ==> (&0:int) < ival result)`;;
