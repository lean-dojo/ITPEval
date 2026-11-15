(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_peekqtvc: a bit-stream peeking verification
  condition relating 32-bit offsets and lengths, 64-bit result bits, byte-list
  bounds, modular additions, and the loop invariant. This file contains no
  proof.
*)

needs "Library/words.ml";;

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
  `!len:int32. !start:int32. !addr:byte list.
     let u32 = \x:int32. (&(val x):int) in
     let bit64 = \(i:int) (x:int64). bit (bitwalker_nat_of_int i) x in
     let bytes = (&8:int) * (&(LENGTH addr):int) in
     u32 len <= (&64:int)
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
        u32 start + u32 len <= bytes
        ==>
        (!i:int.
           (&0:int) <= i /\ i < u32 len
           ==>
           bit64 i (word 0:int64) =
           nth8_stream addr (u32 start + u32 len - i - (&1:int))) /\
        (!i:int.
           u32 len <= i /\ i < (&64:int)
           ==> bit64 i (word 0:int64) = F)
      else
        (u32 len <= (&64:int) \/ word_ule len (word 64:int32)) /\
        (let lstart:int32 = word_sub (word 64:int32) len in
         u32 lstart = (&64:int) - u32 len
         ==>
         (((&0:int) <= (&0:int) /\ (&0:int) <= u32 len) /\
          (!j:int.
             u32 len - (&0:int) <= j /\ j < u32 len
             ==>
             bit64 j (word 0:int64) =
             nth8_stream addr
               (u32 start + u32 len - j - (&1:int))) /\
          (!j:int.
             (&0:int) <= j /\ j < u32 len - (&0:int)
             ==> bit64 j (word 0:int64) = F) /\
          (!j:int.
             u32 len <= j /\ j < (&64:int)
             ==> bit64 j (word 0:int64) = F)) /\
         (!i:int32. !retval:int64.
            (((&0:int) <= u32 i /\ u32 i <= u32 len) /\
             (!j:int.
                u32 len - u32 i <= j /\ j < u32 len
                ==>
                bit64 j retval =
                nth8_stream addr
                  (u32 start + u32 len - j - (&1:int))) /\
             (!j:int.
                (&0:int) <= j /\ j < u32 len - u32 i
                ==> bit64 j retval = F) /\
             (!j:int.
                u32 len <= j /\ j < (&64:int)
                ==> bit64 j retval = F))
            ==>
            if word_ult i len then
              (u32 start + u32 i < (&4294967296:int) \/
               word_ule
                 (word_add
                   (word_zx start:int128)
                   (word_zx i:int128))
                 (word_zx (word 4294967295:int32):int128)) /\
              (u32 (word_add start i) = u32 start + u32 i
               ==>
               (bytes < (&4294967296:int) /\
                u32 (word_add start i) < bytes) /\
               (u32 lstart + u32 i < (&4294967296:int) \/
                word_ule
                  (word_add
                    (word_zx lstart:int128)
                    (word_zx i:int128))
                  (word_zx (word 4294967295:int32):int128)) /\
               (u32 (word_add lstart i) = u32 lstart + u32 i
                ==>
                u32 (word_add lstart i) < (&64:int) /\
                (!o1:int64.
                   ((!i1:int.
                       (((&0:int) <= i1 /\ i1 < (&64:int)) /\
                        ~(i1 =
                          (&63:int) - u32 (word_add lstart i)))
                       ==> bit64 i1 o1 = bit64 i1 retval) /\
                    nth8_stream addr (u32 (word_add start i)) =
                    bit64
                      ((&63:int) - u32 (word_add lstart i))
                      o1)
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
                     u32 len - u32 (word_add i (word 1:int32)) <
                     u32 len - u32 i) /\
                    ((&0:int) <= u32 (word_add i (word 1:int32)) /\
                     u32 (word_add i (word 1:int32)) <= u32 len) /\
                    (!j:int.
                       u32 len - u32 (word_add i (word 1:int32)) <= j /\
                       j < u32 len
                       ==>
                       bit64 j o1 =
                       nth8_stream addr
                         (u32 start + u32 len - j - (&1:int))) /\
                    (!j:int.
                       (&0:int) <= j /\
                       j < u32 len - u32 (word_add i (word 1:int32))
                       ==> bit64 j o1 = F) /\
                    (!j:int.
                       u32 len <= j /\ j < (&64:int)
                       ==> bit64 j o1 = F)))))
            else
              (bytes < u32 start + u32 len
               ==> retval = (word 0:int64)) /\
              (u32 start + u32 len <= bytes
               ==>
               (!i1:int.
                  (&0:int) <= i1 /\ i1 < u32 len
                  ==>
                  bit64 i1 retval =
                  nth8_stream addr
                    (u32 start + u32 len - i1 - (&1:int))) /\
               (!i1:int.
                  u32 len <= i1 /\ i1 < (&64:int)
                  ==> bit64 i1 retval = F)))))`;;
