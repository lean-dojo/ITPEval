(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/queens_bv_Bits_belowqtvc: a 32-bit verification condition identifying
  the low-bit mask below a bounded word with its finite integer-set model and
  preserving that model in the result record. This file contains no proof.
*)

let queens_bv_output = open_out "/dev/null";;
let queens_bv_formatter = Format.formatter_of_out_channel queens_bv_output;;
let queens_bv_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file queens_bv_formatter path);;
let queens_bv_words_loaded =
  Toploop.use_file queens_bv_formatter "Library/words.ml";;
Hol_loader.file_loader := queens_bv_previous_loader;;
Format.pp_print_flush queens_bv_formatter ();;
close_out queens_bv_output;;
if not queens_bv_words_loaded then
  failwith "failed to load Library/words.ml";;

let queens_bv_nat_of_int = new_definition
  `queens_bv_nat_of_int (z:int) =
     if (&0:int) <= z then num_of_int z else 0`;;

let queens_bv_interval = new_definition
  `queens_bv_interval (lower:int) (upper:int) =
     \i:int. lower <= i /\ i < upper`;;

let statement =
  `!bv:A->int32. !mdl:A->int->bool.
     ((!i:int. !self:A.
         (((&0:int) <= i /\ i < (&32:int)) /\
          bit (queens_bv_nat_of_int i) (bv self) <=>
          i IN mdl self)) /\
      (!a b:A.
         bv a = bv b /\ mdl a = mdl b
         ==> a = b))
     ==>
     !n:int32.
       word_ule n (word 32:int32)
       ==>
       let o1 =
         queens_bv_interval (&0:int) (&(val n):int) in
       let o2 =
         word_not
           (word_shl (word 4294967295:int32) (val n)) in
       (!i:int.
          (((&0:int) <= i /\ i < (&32:int)) /\
           bit (queens_bv_nat_of_int i) o2 <=>
           i IN o1)) /\
       (!result:A.
          bv result = o2 /\ mdl result = o1
          ==>
          mdl result =
          queens_bv_interval (&0:int) (&(val n):int))`;;
