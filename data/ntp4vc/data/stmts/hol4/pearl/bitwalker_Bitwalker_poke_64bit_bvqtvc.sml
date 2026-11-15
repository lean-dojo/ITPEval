(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_poke_64bit_bvqtvc: a 64-bit bit-update
  verification condition stating that setting or clearing one selected bit
  preserves every other bit. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory wordsTheory;

val poke_int_to_num_def = Define `
  poke_int_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val poke_uint32_def = Define `
  poke_uint32 (x : word32) = &(w2n x)`;

val bitwalker_Bitwalker_poke_64bit_vc =
  ``!left1 : word32.
    !flag : bool.
    !value : word64.
      poke_uint32 left1 < (64 : int) ==>
      ((poke_uint32 left1 <= (63 : int) \/
        left1 <=+ (63w : word32)) /\
       (let o1 : word32 = (63w : word32) - left1 in
          poke_uint32 o1 = (63 : int) - poke_uint32 left1 ==>
          (let mask : word64 = (1w : word64) << w2n o1 in
             T /\
             !result : word64.
               (if flag then
                  result = value || mask
                else
                  result = value && ~mask) ==>
               ((!i : word32.
                   ~(i = (63w : word32) - left1) ==>
                   word_bit (w2n i) result =
                     word_bit (w2n i) value) /\
                flag =
                  word_bit
                    (w2n ((63w : word32) - left1))
                    result))) /\
       (!result : word64.
          ((!i : word32.
              ~(i = (63w : word32) - left1) ==>
              word_bit (w2n i) result =
                word_bit (w2n i) value) /\
           flag =
             word_bit
               (w2n ((63w : word32) - left1))
               result) ==>
          ((!i : int.
              (((0 : int) <= i /\ i < (64 : int)) /\
               ~(i = (63 : int) - poke_uint32 left1)) ==>
              word_bit (poke_int_to_num i) result =
                word_bit (poke_int_to_num i) value) /\
           flag =
             word_bit
               (poke_int_to_num
                  ((63 : int) - poke_uint32 left1))
               result)))``;
