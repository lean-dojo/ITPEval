(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_poke_8bitqtvc: a fixed-width bit-vector
  verification condition for setting or clearing one selected bit of an
  8-bit byte while preserving the other seven bits, together with the
  equivalent bounded-integer indexing formulation. This file contains no
  proof.
*)

let bitwalker_output = open_out "/dev/null";;
let bitwalker_formatter = Format.formatter_of_out_channel bitwalker_output;;
let previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file bitwalker_formatter path);;
let words_loaded =
  Toploop.use_file bitwalker_formatter "Library/words.ml";;
Hol_loader.file_loader := previous_file_loader;;
Format.pp_print_flush bitwalker_formatter ();;
close_out bitwalker_output;;
if not words_loaded then failwith "failed to load Library/words.ml";;

let bitwalker_nat_of_int = new_definition
  `bitwalker_nat_of_int (z:int) =
     if (&0:int) <= z then num_of_int z else 0`;;

let statement =
  `!left1:int32. !flag:bool. !byte:byte.
     let u32 = \x:int32. (&(val x):int) in
     u32 left1 < (&8:int)
     ==>
     (let o1:byte = word_zx left1 in
      ((&(val o1):int) <= (&7:int) \/
       word_ule o1 (word 7:byte)) /\
      (let o2:byte = word_sub (word 7:byte) o1 in
       (&(val o2):int) = (&7:int) - (&(val o1):int)
       ==>
       (let mask:byte = word_shl (word 1:byte) (val o2) in
        (if flag then T else T) /\
        (!result:byte.
           (if flag
            then result = word_or byte mask
            else result = word_and byte (word_not mask))
           ==>
           (!i:int32.
              word_ult i (word 8:int32)
              ==>
              ~(i = word_sub (word 7:int32) left1)
              ==>
              bit (val (word_zx i:byte)) result =
              bit (val (word_zx i:byte)) byte) /\
           bit
             (val
               (word_sub
                 (word 7:byte)
                 (word_zx left1:byte)))
             result =
           flag)))) /\
     (!result:byte.
        ((!i:int32.
            word_ult i (word 8:int32)
            ==>
            ~(i = word_sub (word 7:int32) left1)
            ==>
            bit (val (word_zx i:byte)) result =
            bit (val (word_zx i:byte)) byte) /\
         bit
           (val
             (word_sub
               (word 7:byte)
               (word_zx left1:byte)))
           result =
         flag)
        ==>
        (!i:int.
           ((&0:int) <= i /\ i < (&8:int))
           ==>
           ~(i = (&7:int) - u32 left1)
           ==>
           bit (bitwalker_nat_of_int i) result =
           bit (bitwalker_nat_of_int i) byte) /\
        bit
          (bitwalker_nat_of_int ((&7:int) - u32 left1))
          result =
        flag)`;;
