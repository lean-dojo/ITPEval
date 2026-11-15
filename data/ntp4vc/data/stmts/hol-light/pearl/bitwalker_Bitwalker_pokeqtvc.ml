(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_pokeqtvc: a bit-stream poke verification
  condition relating 32-bit positions and lengths, a 64-bit value, bounded
  byte streams, result-status cases, and the loop invariant preserving all
  unaffected stream bits. This file contains no proof.
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
  `!len:int32. !start:int32. !addr:byte list. !value:int64.
     let u32 = \x:int32. (&(val x):int) in
     let u64 = \x:int64. (&(val x):int) in
     let bit64 = \(i:int) (x:int64). bit (bitwalker_nat_of_int i) x in
     let bytes = (&8:int) * (&(LENGTH addr):int) in
     u32 len < (&64:int)
     ==>
     u32 start + u32 len < (&4294967296:int)
     ==>
     bytes < (&4294967296:int)
     ==>
     (u32 start + u32 len < (&4294967296:int) \/
      word_ule
        (word_add (word_zx start:int128) (word_zx len:int128))
        (word_zx (word 4294967295:int32):int128)) /\
     (u32 (word_add start len) = u32 start + u32 len
      ==>
      if bytes < u32 (word_add start len) then
        ((--(&2:int) <= --(&1:int) /\ --(&1:int) <= (&0:int)) /\
         bytes < u32 start + u32 len /\
         ((--(&1:int) = --(&2:int)) <=>
          u64 (maxvalue len) <= u64 value /\
          u32 start + u32 len <= bytes) /\
         ((--(&1:int) = (&0:int)) <=>
          u64 value < u64 (maxvalue len) /\
          u32 start + u32 len <= bytes) /\
         (--(&1:int) = (&0:int)
          ==>
          (!i:int.
             u32 start <= i /\ i < u32 start + u32 len
             ==>
             nth8_stream addr i =
             bit64 (u32 len - i - (&1:int) + u32 start) value)))
      else if word_ule (maxvalue len) value then
        ((--(&2:int) <= --(&2:int) /\ --(&2:int) <= (&0:int)) /\
         ((--(&2:int) = --(&1:int)) <=>
          bytes < u32 start + u32 len) /\
         (u64 (maxvalue len) <= u64 value /\
          u32 start + u32 len <= bytes) /\
         ((--(&2:int) = (&0:int)) <=>
          u64 value < u64 (maxvalue len) /\
          u32 start + u32 len <= bytes) /\
         (--(&2:int) = (&0:int)
          ==>
          (!i:int.
             u32 start <= i /\ i < u32 start + u32 len
             ==>
             nth8_stream addr i =
             bit64 (u32 len - i - (&1:int) + u32 start) value)))
      else
        (u32 len <= (&64:int) \/
         word_ule len (word 64:int32)) /\
        (let lstart:int32 = word_sub (word 64:int32) len in
         u32 lstart = (&64:int) - u32 len
         ==>
         ((((&0:int) <= (&0:int) /\ (&0:int) <= u32 len) /\
           (!j:int.
              u32 start <= j /\ j < u32 start + (&0:int)
              ==>
              nth8_stream addr j =
              bit64 (u32 len - j - (&1:int) + u32 start) value)) /\
          (!i:int32. !addr1:byte list.
             LENGTH addr1 = LENGTH addr
             ==>
             (((&0:int) <= u32 i /\ u32 i <= u32 len) /\
              (!j:int.
                 (&0:int) <= j /\ j < u32 start
                 ==> nth8_stream addr j = nth8_stream addr1 j) /\
              (!j:int.
                 u32 start <= j /\ j < u32 start + u32 i
                 ==>
                 nth8_stream addr1 j =
                 bit64 (u32 len - j - (&1:int) + u32 start) value) /\
              (!j:int.
                 u32 start + u32 i <= j /\
                 j < (&8:int) * (&(LENGTH addr1):int)
                 ==> nth8_stream addr1 j = nth8_stream addr j))
             ==>
             if word_ult i len then
               (u32 lstart + u32 i < (&4294967296:int) \/
                word_ule
                  (word_add
                    (word_zx lstart:int128)
                    (word_zx i:int128))
                  (word_zx (word 4294967295:int32):int128)) /\
               (u32 (word_add lstart i) = u32 lstart + u32 i
                ==>
                u32 (word_add lstart i) < (&64:int) /\
                (u32 start + u32 i < (&4294967296:int) \/
                 word_ule
                   (word_add
                     (word_zx start:int128)
                     (word_zx i:int128))
                   (word_zx (word 4294967295:int32):int128)) /\
                (u32 (word_add start i) = u32 start + u32 i
                 ==>
                 (((&8:int) * (&(LENGTH addr1):int) <
                   (&4294967296:int)) /\
                  u32 (word_add start i) <
                  (&8:int) * (&(LENGTH addr1):int)) /\
                 (!addr2:byte list.
                    LENGTH addr2 = LENGTH addr1
                    ==>
                    (((!i1:int.
                         (&0:int) <= i1 /\
                         i1 < (&8:int) * (&(LENGTH addr2):int)
                         ==>
                         ~(i1 = u32 (word_add start i))
                         ==>
                         nth8_stream addr2 i1 =
                         nth8_stream addr1 i1) /\
                      nth8_stream addr2 (u32 (word_add start i)) =
                      bit64
                        ((&63:int) - u32 (word_add lstart i))
                        value)
                     ==>
                     (u32 i + (&1:int) < (&4294967296:int) \/
                      word_ule
                        (word_add
                          (word_zx i:int128)
                          (word_zx (word 1:int32):int128))
                        (word_zx (word 4294967295:int32):int128)) /\
                     (u32 (word_add i (word 1:int32)) =
                      u32 i + (&1:int)
                      ==>
                      ((&0:int) <= u32 len - u32 i /\
                       u32 len -
                       u32 (word_add i (word 1:int32)) <
                       u32 len - u32 i) /\
                      ((&0:int) <= u32 (word_add i (word 1:int32)) /\
                       u32 (word_add i (word 1:int32)) <= u32 len) /\
                      (!j:int.
                         (&0:int) <= j /\ j < u32 start
                         ==>
                         nth8_stream addr j = nth8_stream addr2 j) /\
                      (!j:int.
                         u32 start <= j /\
                         j <
                         u32 start +
                         u32 (word_add i (word 1:int32))
                         ==>
                         nth8_stream addr2 j =
                         bit64
                           (u32 len - j - (&1:int) + u32 start)
                           value) /\
                      (!j:int.
                         u32 start +
                         u32 (word_add i (word 1:int32)) <= j /\
                         j < (&8:int) * (&(LENGTH addr2):int)
                         ==>
                         nth8_stream addr2 j =
                         nth8_stream addr j))))))
             else
               ((--(&2:int) <= (&0:int) /\ (&0:int) <= (&0:int)) /\
                (((&0:int) = --(&1:int)) <=>
                 (&8:int) * (&(LENGTH addr1):int) <
                 u32 start + u32 len) /\
                (((&0:int) = --(&2:int)) <=>
                 u64 (maxvalue len) <= u64 value /\
                 u32 start + u32 len <=
                 (&8:int) * (&(LENGTH addr1):int)) /\
                (u64 value < u64 (maxvalue len) /\
                 u32 start + u32 len <=
                 (&8:int) * (&(LENGTH addr1):int)) /\
                (!i1:int.
                   (&0:int) <= i1 /\ i1 < u32 start
                   ==> nth8_stream addr i1 = nth8_stream addr1 i1) /\
                (!i1:int.
                   u32 start <= i1 /\ i1 < u32 start + u32 len
                   ==>
                   nth8_stream addr1 i1 =
                   bit64
                     (u32 len - i1 - (&1:int) + u32 start)
                     value) /\
                (!i1:int.
                   u32 start + u32 len <= i1 /\
                   i1 < (&8:int) * (&(LENGTH addr1):int)
                   ==> nth8_stream addr1 i1 = nth8_stream addr i1))))))`;;
