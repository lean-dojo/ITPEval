(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_pokethenpeekqtvc: a bit-stream poke-then-peek
  verification condition relating bounded byte streams, 32-bit positions and
  lengths, a 64-bit value, result-status cases, preservation of unaffected
  bits, and recovery of the written value. This file contains no proof.
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

let nth8_stream = new_definition
  `nth8_stream (stream:byte list) (pos:int) =
     let byte_index = bitwalker_nat_of_int (pos div (&8:int)) in
     let octet:byte =
       if byte_index < LENGTH stream
       then EL byte_index stream
       else word 0 in
     bit (bitwalker_nat_of_int ((&7:int) - pos rem (&8:int))) octet`;;

let maxvalue = new_definition
  `maxvalue (len:int32) =
     word_shl (word 1:int64) (val (word_zx len:int64))`;;

let statement =
  `!addr:byte list. !len:int32. !start:int32. !value:int64.
     let u32 = \x:int32. (&(val x):int) in
     let u64 = \x:int64. (&(val x):int) in
     let bit64 = \(i:int) (x:int64). bit (bitwalker_nat_of_int i) x in
     let bytes = (&8:int) * (&(LENGTH addr):int) in
     bytes < (&4294967296:int)
     ==> (&0:int) <= u32 len
     ==> u32 len < (&64:int)
     ==> u32 start + u32 len <= bytes
     ==> u64 value < u64 (maxvalue len)
     ==> u32 len < (&64:int) /\
         u32 start + u32 len < (&4294967296:int) /\
         bytes < (&4294967296:int) /\
         (!addr1:byte list.
            LENGTH addr1 = LENGTH addr
            ==>
            !poke_result:int.
              (((--(&2:int) <= poke_result /\ poke_result <= (&0:int)) /\
                (poke_result = --(&1:int) <=>
                 (&8:int) * (&(LENGTH addr1):int) <
                 u32 start + u32 len) /\
                (poke_result = --(&2:int) <=>
                 u64 (maxvalue len) <= u64 value /\
                 u32 start + u32 len <=
                 (&8:int) * (&(LENGTH addr1):int)) /\
                (poke_result = (&0:int) <=>
                 u64 value < u64 (maxvalue len) /\
                 u32 start + u32 len <=
                 (&8:int) * (&(LENGTH addr1):int)) /\
                (poke_result = (&0:int)
                 ==>
                 (!i:int.
                    (&0:int) <= i /\ i < u32 start
                    ==> nth8_stream addr i = nth8_stream addr1 i) /\
                 (!i:int.
                    u32 start <= i /\ i < u32 start + u32 len
                    ==>
                    nth8_stream addr1 i =
                    bit64
                      (u32 len - i - (&1:int) + u32 start)
                      value) /\
                 (!i:int.
                    u32 start + u32 len <= i /\
                    i < (&8:int) * (&(LENGTH addr1):int)
                    ==> nth8_stream addr1 i = nth8_stream addr i)))
               ==>
               (u32 len <= (&64:int) /\
                u32 start + u32 len < (&4294967296:int) /\
                (&8:int) * (&(LENGTH addr1):int) <
                (&4294967296:int)) /\
               (!peek_result:int64.
                  ((((&8:int) * (&(LENGTH addr1):int) <
                     u32 start + u32 len
                     ==> peek_result = (word 0:int64)) /\
                    (u32 start + u32 len <=
                     (&8:int) * (&(LENGTH addr1):int)
                     ==>
                     (!i:int.
                        (&0:int) <= i /\ i < u32 len
                        ==>
                        bit64 i peek_result =
                        nth8_stream
                          addr1
                          (u32 start + u32 len - i - (&1:int))) /\
                     (!i:int.
                        u32 len <= i /\ i < (&64:int)
                        ==> bit64 i peek_result = F)))
                   ==> peek_result = value))))`;;
