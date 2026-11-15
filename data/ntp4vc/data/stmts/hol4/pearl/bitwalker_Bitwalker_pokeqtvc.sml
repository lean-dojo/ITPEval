(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_pokeqtvc: a bitstream poke verification condition
  over 8-bit address words, 32-bit positions and lengths, and a 64-bit value,
  including overflow checks and the bit-writing loop invariant. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory wordsTheory;

val poke_int_to_num_def = Define `
  poke_int_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val poke_uint32_def = Define `
  poke_uint32 (x : word32) = &(w2n x)`;

val poke_uint64_def = Define `
  poke_uint64 (x : word64) = &(w2n x)`;

val poke_addr_bits_def = Define `
  poke_addr_bits (addr : word8 list) =
    (8 : int) * &(LENGTH addr)`;

val poke_nth8_stream_def = Define `
  poke_nth8_stream (stream : word8 list) (pos : int) =
    let byte_index = poke_int_to_num (pos / 8) in
    let byte =
      if byte_index < LENGTH stream then
        EL byte_index stream
      else
        (0w : word8)
    in
      word_bit (poke_int_to_num (7 - pos % 8)) byte`;

val poke_maxvalue_def = Define `
  poke_maxvalue (len : word32) =
    (1w : word64) << w2n len`;

val poke_overflow32_def = Define `
  poke_overflow32 (x : word32) (y : word32) <=>
    poke_uint32 x + poke_uint32 y < (4294967296 : int) \/
    w2n ((w2w x : 128 word) + (w2w y : 128 word)) <=
      w2n (w2w (4294967295w : word32) : 128 word)`;

val poke_no_wrap32_def = Define `
  poke_no_wrap32 (x : word32) (y : word32) <=>
    poke_uint32 (x + y) = poke_uint32 x + poke_uint32 y`;

val poke_value_bit_def = Define `
  poke_value_bit
    (len : word32)
    (start : word32)
    (value : word64)
    (i : int) =
      word_bit
        (poke_int_to_num
           (poke_uint32 len - i - 1 + poke_uint32 start))
        value`;

val poke_inv_def = Define `
  poke_inv
    (addr : word8 list)
    (addr1 : word8 list)
    (start : word32)
    (len : word32)
    (i : word32)
    (value : word64) <=>
      ((0 : int) <= poke_uint32 i /\
       poke_uint32 i <= poke_uint32 len) /\
      (!j : int.
         (0 : int) <= j /\ j < poke_uint32 start ==>
         poke_nth8_stream addr j =
           poke_nth8_stream addr1 j) /\
      (!j : int.
         poke_uint32 start <= j /\
         j < poke_uint32 start + poke_uint32 i ==>
         poke_nth8_stream addr1 j =
           poke_value_bit len start value j) /\
      (!j : int.
         poke_uint32 start + poke_uint32 i <= j /\
         j < poke_addr_bits addr1 ==>
         poke_nth8_stream addr1 j =
           poke_nth8_stream addr j)`;

val poke_initial_def = Define `
  poke_initial
    (addr : word8 list)
    (start : word32)
    (len : word32)
    (value : word64) <=>
      ((0 : int) <= (0 : int) /\
       (0 : int) <= poke_uint32 len) /\
      (!j : int.
         poke_uint32 start <= j /\
         j < poke_uint32 start + (0 : int) ==>
         poke_nth8_stream addr j =
           poke_value_bit len start value j)`;

val poke_update_def = Define `
  poke_update
    (addr1 : word8 list)
    (addr2 : word8 list)
    (start : word32)
    (lstart : word32)
    (i : word32)
    (value : word64) <=>
      (!i1 : int.
         (0 : int) <= i1 /\ i1 < poke_addr_bits addr2 ==>
         ~(i1 = poke_uint32 (start + i)) ==>
         poke_nth8_stream addr2 i1 =
           poke_nth8_stream addr1 i1) /\
      poke_nth8_stream addr2 (poke_uint32 (start + i)) =
        word_bit
          (poke_int_to_num
             ((63 : int) - poke_uint32 (lstart + i)))
          value`;

val poke_final_def = Define `
  poke_final
    (addr : word8 list)
    (addr1 : word8 list)
    (start : word32)
    (len : word32)
    (value : word64) <=>
      ((~2 : int) <= (0 : int) /\ (0 : int) <= (0 : int)) /\
      ((0 : int) = (~1 : int) <=>
       poke_addr_bits addr1 <
         poke_uint32 start + poke_uint32 len) /\
      ((0 : int) = (~2 : int) <=>
       poke_uint64 (poke_maxvalue len) <= poke_uint64 value /\
       poke_uint32 start + poke_uint32 len <=
         poke_addr_bits addr1) /\
      (poke_uint64 value < poke_uint64 (poke_maxvalue len) /\
       poke_uint32 start + poke_uint32 len <=
         poke_addr_bits addr1) /\
      (!i1 : int.
         (0 : int) <= i1 /\ i1 < poke_uint32 start ==>
         poke_nth8_stream addr i1 =
           poke_nth8_stream addr1 i1) /\
      (!i1 : int.
         poke_uint32 start <= i1 /\
         i1 < poke_uint32 start + poke_uint32 len ==>
         poke_nth8_stream addr1 i1 =
           poke_value_bit len start value i1) /\
      (!i1 : int.
         poke_uint32 start + poke_uint32 len <= i1 /\
         i1 < poke_addr_bits addr1 ==>
         poke_nth8_stream addr1 i1 =
           poke_nth8_stream addr i1)`;

val poke_loop_step_def = Define `
  poke_loop_step
    (addr : word8 list)
    (addr1 : word8 list)
    (start : word32)
    (len : word32)
    (lstart : word32)
    (i : word32)
    (value : word64) <=>
      if i <+ len then
        poke_overflow32 lstart i /\
        (poke_no_wrap32 lstart i ==>
         poke_uint32 (lstart + i) < (64 : int) /\
         poke_overflow32 start i /\
         (poke_no_wrap32 start i ==>
          (poke_addr_bits addr1 < (4294967296 : int) /\
           poke_uint32 (start + i) < poke_addr_bits addr1) /\
          (!addr2 : word8 list.
             LENGTH addr2 = LENGTH addr1 ==>
             poke_update addr1 addr2 start lstart i value ==>
             poke_overflow32 i (1w : word32) /\
             (poke_no_wrap32 i (1w : word32) ==>
              ((0 : int) <= poke_uint32 len - poke_uint32 i /\
               poke_uint32 len -
                   poke_uint32 (i + (1w : word32)) <
                 poke_uint32 len - poke_uint32 i) /\
              poke_inv
                addr addr2 start len
                (i + (1w : word32)) value))))
      else
        poke_final addr addr1 start len value`;

val bitwalker_Bitwalker_poke_vc =
  ``!len start : word32.
    !addr : word8 list.
    !value : word64.
      poke_uint32 len < (64 : int) ==>
      poke_uint32 start + poke_uint32 len <
        (4294967296 : int) ==>
      poke_addr_bits addr < (4294967296 : int) ==>
      poke_overflow32 start len /\
      (poke_no_wrap32 start len ==>
       if poke_addr_bits addr < poke_uint32 (start + len) then
         ((~2 : int) <= (~1 : int) /\
          (~1 : int) <= (0 : int)) /\
         poke_addr_bits addr <
           poke_uint32 start + poke_uint32 len /\
         ((~1 : int) = (~2 : int) <=>
          poke_uint64 (poke_maxvalue len) <= poke_uint64 value /\
          poke_uint32 start + poke_uint32 len <=
            poke_addr_bits addr) /\
         ((~1 : int) = (0 : int) <=>
          poke_uint64 value < poke_uint64 (poke_maxvalue len) /\
          poke_uint32 start + poke_uint32 len <=
            poke_addr_bits addr) /\
         ((~1 : int) = (0 : int) ==>
          (!i : int.
             poke_uint32 start <= i /\
             i < poke_uint32 start + poke_uint32 len ==>
             poke_nth8_stream addr i =
               poke_value_bit len start value i))
       else if
         poke_uint64 (poke_maxvalue len) <= poke_uint64 value
       then
         ((~2 : int) <= (~2 : int) /\
          (~2 : int) <= (0 : int)) /\
         ((~2 : int) = (~1 : int) <=>
          poke_addr_bits addr <
            poke_uint32 start + poke_uint32 len) /\
         (poke_uint64 (poke_maxvalue len) <= poke_uint64 value /\
          poke_uint32 start + poke_uint32 len <=
            poke_addr_bits addr) /\
         ((~2 : int) = (0 : int) <=>
          poke_uint64 value < poke_uint64 (poke_maxvalue len) /\
          poke_uint32 start + poke_uint32 len <=
            poke_addr_bits addr) /\
         ((~2 : int) = (0 : int) ==>
          (!i : int.
             poke_uint32 start <= i /\
             i < poke_uint32 start + poke_uint32 len ==>
             poke_nth8_stream addr i =
               poke_value_bit len start value i))
       else
         (poke_uint32 len <= (64 : int) \/
          len <=+ (64w : word32)) /\
         (let lstart : word32 = (64w : word32) - len in
            poke_uint32 lstart =
                (64 : int) - poke_uint32 len ==>
            poke_initial addr start len value /\
            (!i : word32.
             !addr1 : word8 list.
               LENGTH addr1 = LENGTH addr ==>
               poke_inv addr addr1 start len i value ==>
               poke_loop_step
                 addr addr1 start len lstart i value)))``;
