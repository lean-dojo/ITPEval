(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/queens_bv_Bits_rightmost_bit_trickqtvc: a 32-bit verification
  condition stating that a nonzero word AND its two's-complement negation has
  exactly the least set bit in its finite integer-set model. This file contains
  no proof.
*)

let queens_bv_rightmost_output = open_out "/dev/null";;
let queens_bv_rightmost_formatter =
  Format.formatter_of_out_channel queens_bv_rightmost_output;;
let queens_bv_rightmost_previous_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file queens_bv_rightmost_formatter path);;
let queens_bv_rightmost_words_loaded =
  Toploop.use_file queens_bv_rightmost_formatter "Library/words.ml";;
Hol_loader.file_loader := queens_bv_rightmost_previous_loader;;
Format.pp_print_flush queens_bv_rightmost_formatter ();;
close_out queens_bv_rightmost_output;;
if not queens_bv_rightmost_words_loaded then
  failwith "failed to load Library/words.ml";;

let queens_bv_rightmost_nat_of_int = new_definition
  `queens_bv_rightmost_nat_of_int (z:int) =
     if (&0:int) <= z then num_of_int z else 0`;;

let queens_bv_rightmost_minimum = new_definition
  `queens_bv_rightmost_minimum (s:int->bool) =
     @m:int. m IN s /\ (!j:int. j IN s ==> m <= j)`;;

let statement =
  `!bv:A->int32. !mdl:A->int->bool.
     ((!i:int. !self:A.
         (((&0:int) <= i /\ i < (&32:int)) /\
          bit (queens_bv_rightmost_nat_of_int i) (bv self) <=>
          i IN mdl self)) /\
      (!a b:A.
         bv a = bv b /\ mdl a = mdl b
         ==> a = b))
     ==>
     !a:A.
       ~(mdl a = {})
       ==>
       let res =
         word_and (bv a) (word_neg (bv a)) in
       let minimum =
         queens_bv_rightmost_minimum (mdl a) in
       let o1 =
         minimum INSERT ({}:int->bool) in
       (!i:int.
          (((&0:int) <= i /\ i < (&32:int)) /\
           bit (queens_bv_rightmost_nat_of_int i) res <=>
           i IN o1)) /\
       (!result:A.
          bv result = res /\ mdl result = o1
          ==>
          mdl result =
          minimum INSERT ({}:int->bool))`;;
