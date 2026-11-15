(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_poke_8bitqtvc: an 8-bit bit-update verification
  condition stating that setting or clearing one selected bit preserves every
  other bit. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory wordsTheory;

val poke8_int_to_num_def = Define `
  poke8_int_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val poke8_uint32_def = Define `
  poke8_uint32 (x : word32) = &(w2n x)`;

val poke8_uint8_def = Define `
  poke8_uint8 (x : word8) = &(w2n x)`;

val bitwalker_Bitwalker_poke_8bit_vc =
  ``!left1 : word32.
    !flag : bool.
    !byte : word8.
      poke8_uint32 left1 < (8 : int) ==>
      ((let o1 : word8 = w2w left1 in
          (poke8_uint8 o1 <= (7 : int) \/
           o1 <=+ (7w : word8)) /\
          (let o2 : word8 = (7w : word8) - o1 in
             poke8_uint8 o2 = (7 : int) - poke8_uint8 o1 ==>
             (let mask : word8 = (1w : word8) << w2n o2 in
                T /\
                !result : word8.
                  (if flag then
                     result = byte || mask
                   else
                     result = byte && ~mask) ==>
                  ((!i : word32.
                      i <+ (8w : word32) ==>
                      ~(i = (7w : word32) - left1) ==>
                      word_bit (w2n (w2w i : word8)) result =
                        word_bit (w2n (w2w i : word8)) byte) /\
                   word_bit
                     (w2n
                        ((7w : word8) -
                         (w2w left1 : word8)))
                     result =
                     flag)))) /\
       (!result : word8.
          ((!i : word32.
              i <+ (8w : word32) ==>
              ~(i = (7w : word32) - left1) ==>
              word_bit (w2n (w2w i : word8)) result =
                word_bit (w2n (w2w i : word8)) byte) /\
           word_bit
             (w2n
                ((7w : word8) -
                 (w2w left1 : word8)))
             result =
             flag) ==>
          ((!i : int.
              (((0 : int) <= i /\ i < (8 : int)) /\
               ~(i = (7 : int) - poke8_uint32 left1)) ==>
              word_bit (poke8_int_to_num i) result =
                word_bit (poke8_int_to_num i) byte) /\
           word_bit
             (poke8_int_to_num
                ((7 : int) - poke8_uint32 left1))
             result =
             flag)))``;
