(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_pokethenpeekqtvc: a bitstream poke-then-peek
  verification condition over 8-bit address words, 32-bit positions and
  lengths, and a 64-bit value, relating the written bits to the value read
  back. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory wordsTheory;

val pokethenpeek_int_to_num_def = Define `
  pokethenpeek_int_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val pokethenpeek_uint32_def = Define `
  pokethenpeek_uint32 (x : word32) = &(w2n x)`;

val pokethenpeek_uint64_def = Define `
  pokethenpeek_uint64 (x : word64) = &(w2n x)`;

val pokethenpeek_addr_bits_def = Define `
  pokethenpeek_addr_bits (addr : word8 list) =
    (8 : int) * &(LENGTH addr)`;

val pokethenpeek_nth8_stream_def = Define `
  pokethenpeek_nth8_stream (stream : word8 list) (pos : int) =
    let byte_index = pokethenpeek_int_to_num (pos / 8) in
    let byte =
      if byte_index < LENGTH stream then
        EL byte_index stream
      else
        (0w : word8)
    in
      word_bit
        (pokethenpeek_int_to_num (7 - pos % 8))
        byte`;

val pokethenpeek_maxvalue_def = Define `
  pokethenpeek_maxvalue (len : word32) =
    (1w : word64) << w2n len`;

val pokethenpeek_value_bit_def = Define `
  pokethenpeek_value_bit
    (len : word32)
    (start : word32)
    (value : word64)
    (i : int) =
      word_bit
        (pokethenpeek_int_to_num
           (pokethenpeek_uint32 len - i - 1 +
            pokethenpeek_uint32 start))
        value`;

val bitwalker_Bitwalker_pokethenpeek_vc =
  ``!addr : word8 list.
    !len start : word32.
    !value : word64.
      pokethenpeek_addr_bits addr < (4294967296 : int) ==>
      (0 : int) <= pokethenpeek_uint32 len ==>
      pokethenpeek_uint32 len < (64 : int) ==>
      pokethenpeek_uint32 start + pokethenpeek_uint32 len <=
        pokethenpeek_addr_bits addr ==>
      pokethenpeek_uint64 value <
        pokethenpeek_uint64 (pokethenpeek_maxvalue len) ==>
      pokethenpeek_uint32 len < (64 : int) /\
      pokethenpeek_uint32 start + pokethenpeek_uint32 len <
        (4294967296 : int) /\
      pokethenpeek_addr_bits addr < (4294967296 : int) /\
      !addr1 : word8 list.
        LENGTH addr1 = LENGTH addr ==>
        !poke_result : int.
          (((~2 : int) <= poke_result /\
            poke_result <= (0 : int)) /\
           (poke_result = (~1 : int) <=>
            pokethenpeek_addr_bits addr1 <
              pokethenpeek_uint32 start +
              pokethenpeek_uint32 len) /\
           (poke_result = (~2 : int) <=>
            pokethenpeek_uint64 (pokethenpeek_maxvalue len) <=
              pokethenpeek_uint64 value /\
            pokethenpeek_uint32 start +
              pokethenpeek_uint32 len <=
              pokethenpeek_addr_bits addr1) /\
           (poke_result = (0 : int) <=>
            pokethenpeek_uint64 value <
              pokethenpeek_uint64 (pokethenpeek_maxvalue len) /\
            pokethenpeek_uint32 start +
              pokethenpeek_uint32 len <=
              pokethenpeek_addr_bits addr1) /\
           (poke_result = (0 : int) ==>
            (!i : int.
               (0 : int) <= i /\
               i < pokethenpeek_uint32 start ==>
               pokethenpeek_nth8_stream addr i =
                 pokethenpeek_nth8_stream addr1 i) /\
            (!i : int.
               pokethenpeek_uint32 start <= i /\
               i <
                 pokethenpeek_uint32 start +
                 pokethenpeek_uint32 len ==>
               pokethenpeek_nth8_stream addr1 i =
                 pokethenpeek_value_bit
                   len start value i) /\
            (!i : int.
               pokethenpeek_uint32 start +
                 pokethenpeek_uint32 len <= i /\
               i < pokethenpeek_addr_bits addr1 ==>
               pokethenpeek_nth8_stream addr1 i =
                 pokethenpeek_nth8_stream addr i))) ==>
          (pokethenpeek_uint32 len <= (64 : int) /\
           pokethenpeek_uint32 start +
             pokethenpeek_uint32 len <
             (4294967296 : int) /\
           pokethenpeek_addr_bits addr1 <
             (4294967296 : int)) /\
          !peek_result : word64.
            ((pokethenpeek_addr_bits addr1 <
                pokethenpeek_uint32 start +
                pokethenpeek_uint32 len ==>
              peek_result = (0w : word64)) /\
             (pokethenpeek_uint32 start +
                pokethenpeek_uint32 len <=
                pokethenpeek_addr_bits addr1 ==>
              (!i : int.
                 (0 : int) <= i /\
                 i < pokethenpeek_uint32 len ==>
                 word_bit
                   (pokethenpeek_int_to_num i)
                   peek_result =
                   pokethenpeek_nth8_stream
                     addr1
                     (pokethenpeek_uint32 start +
                      pokethenpeek_uint32 len - i - 1)) /\
              (!i : int.
                 pokethenpeek_uint32 len <= i /\
                 i < (64 : int) ==>
                 word_bit
                   (pokethenpeek_int_to_num i)
                   peek_result = F))) ==>
            peek_result = value``;
