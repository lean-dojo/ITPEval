(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_peekthenpokeqtvc: a bitstream peek-then-poke
  verification condition over 8-bit input words, 32-bit positions and
  lengths, a 64-bit value, and preservation of all addressed bits. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory wordsTheory;

val peekthenpoke_int_to_num_def = Define `
  peekthenpoke_int_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val peekthenpoke_uint32_def = Define `
  peekthenpoke_uint32 (x : word32) = &(w2n x)`;

val peekthenpoke_uint64_def = Define `
  peekthenpoke_uint64 (x : word64) = &(w2n x)`;

val peekthenpoke_addr_bits_def = Define `
  peekthenpoke_addr_bits (addr : word8 list) =
    (8 : int) * &(LENGTH addr)`;

val peekthenpoke_nth8_stream_def = Define `
  peekthenpoke_nth8_stream (stream : word8 list) (pos : int) =
    let byte_index = peekthenpoke_int_to_num (pos / 8) in
    let byte =
      if byte_index < LENGTH stream then
        EL byte_index stream
      else
        (0w : word8)
    in
      word_bit
        (peekthenpoke_int_to_num (7 - pos % 8))
        byte`;

val peekthenpoke_maxvalue_def = Define `
  peekthenpoke_maxvalue (len : word32) =
    (1w : word64) << w2n len`;

val bitwalker_Bitwalker_peekthenpoke_vc =
  ``!addr : word8 list.
    !len start : word32.
      peekthenpoke_addr_bits addr < (4294967296 : int) ==>
      (0 : int) <= peekthenpoke_uint32 len ==>
      peekthenpoke_uint32 len < (64 : int) ==>
      peekthenpoke_uint32 start + peekthenpoke_uint32 len <=
        peekthenpoke_addr_bits addr ==>
      peekthenpoke_uint32 len <= (64 : int) /\
      peekthenpoke_uint32 start + peekthenpoke_uint32 len <
        (4294967296 : int) /\
      peekthenpoke_addr_bits addr < (4294967296 : int) /\
      !value : word64.
        (peekthenpoke_addr_bits addr <
           peekthenpoke_uint32 start + peekthenpoke_uint32 len ==>
         value = (0w : word64)) /\
        (peekthenpoke_uint32 start + peekthenpoke_uint32 len <=
           peekthenpoke_addr_bits addr ==>
         (!i : int.
            (0 : int) <= i /\ i < peekthenpoke_uint32 len ==>
            word_bit (peekthenpoke_int_to_num i) value =
              peekthenpoke_nth8_stream
                addr
                (peekthenpoke_uint32 start +
                 peekthenpoke_uint32 len - i - 1)) /\
         (!i : int.
            peekthenpoke_uint32 len <= i /\ i < (64 : int) ==>
            word_bit (peekthenpoke_int_to_num i) value = F)) ==>
        (peekthenpoke_uint32 len < (64 : int) /\
         peekthenpoke_uint32 start + peekthenpoke_uint32 len <
           (4294967296 : int) /\
         peekthenpoke_addr_bits addr < (4294967296 : int)) /\
        !addr1 : word8 list.
          LENGTH addr1 = LENGTH addr ==>
          !res : int.
            ((~2 : int) <= res /\ res <= (0 : int)) /\
            (res = (~1 : int) <=>
             peekthenpoke_addr_bits addr1 <
               peekthenpoke_uint32 start + peekthenpoke_uint32 len) /\
            (res = (~2 : int) <=>
             peekthenpoke_uint64 (peekthenpoke_maxvalue len) <=
               peekthenpoke_uint64 value /\
             peekthenpoke_uint32 start + peekthenpoke_uint32 len <=
               peekthenpoke_addr_bits addr1) /\
            (res = (0 : int) <=>
             peekthenpoke_uint64 value <
               peekthenpoke_uint64 (peekthenpoke_maxvalue len) /\
             peekthenpoke_uint32 start + peekthenpoke_uint32 len <=
               peekthenpoke_addr_bits addr1) /\
            (res = (0 : int) ==>
             (!i : int.
                (0 : int) <= i /\ i < peekthenpoke_uint32 start ==>
                peekthenpoke_nth8_stream addr i =
                  peekthenpoke_nth8_stream addr1 i) /\
             (!i : int.
                peekthenpoke_uint32 start <= i /\
                i <
                  peekthenpoke_uint32 start +
                  peekthenpoke_uint32 len ==>
                peekthenpoke_nth8_stream addr1 i =
                  word_bit
                    (peekthenpoke_int_to_num
                       (peekthenpoke_uint32 len - i - 1 +
                        peekthenpoke_uint32 start))
                    value) /\
             (!i : int.
                peekthenpoke_uint32 start +
                  peekthenpoke_uint32 len <= i /\
                i < peekthenpoke_addr_bits addr1 ==>
                peekthenpoke_nth8_stream addr1 i =
                  peekthenpoke_nth8_stream addr i)) ==>
            res = (0 : int) /\
            !i : int.
              (0 : int) <= i /\ i < peekthenpoke_addr_bits addr1 ==>
              peekthenpoke_nth8_stream addr1 i =
                peekthenpoke_nth8_stream addr i``;
