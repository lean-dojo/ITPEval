(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitwalker_Bitwalker_peekqtvc: a bitstream peek verification condition
  over 8-bit input words, 32-bit positions and lengths, and a 64-bit result,
  including overflow checks and the bit-copying loop invariant. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory wordsTheory;

val peek_int_to_num_def = Define `
  peek_int_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val peek_uint32_def = Define `
  peek_uint32 (x : word32) = &(w2n x)`;

val peek_uint64_def = Define `
  peek_uint64 (x : word64) = &(w2n x)`;

val peek_addr_bits_def = Define `
  peek_addr_bits (addr : word8 list) =
    (8 : int) * &(LENGTH addr)`;

val nth8_stream_def = Define `
  nth8_stream (stream : word8 list) (pos : int) =
    let byte_index = peek_int_to_num (pos / 8) in
    let byte =
      if byte_index < LENGTH stream then
        EL byte_index stream
      else
        (0w : word8)
    in
      word_bit (peek_int_to_num (7 - pos % 8)) byte`;

val bitwalker_maxvalue_def = Define `
  bitwalker_maxvalue (len : word32) =
    (1w : word64) << w2n len`;

val peek_overflow32_def = Define `
  peek_overflow32 (x : word32) (y : word32) <=>
    peek_uint32 x + peek_uint32 y < (4294967296 : int) \/
    w2n ((w2w x : 128 word) + (w2w y : 128 word)) <=
      w2n (w2w (4294967295w : word32) : 128 word)`;

val peek_no_wrap32_def = Define `
  peek_no_wrap32 (x : word32) (y : word32) <=>
    peek_uint32 (x + y) = peek_uint32 x + peek_uint32 y`;

val peek_inv_def = Define `
  peek_inv
    (addr : word8 list)
    (start : word32)
    (len : word32)
    (i : word32)
    (retval : word64) <=>
      ((0 : int) <= peek_uint32 i /\
       peek_uint32 i <= peek_uint32 len) /\
      (!j : int.
         peek_uint32 len - peek_uint32 i <= j /\
         j < peek_uint32 len ==>
         word_bit (peek_int_to_num j) retval =
           nth8_stream addr
             (peek_uint32 start + peek_uint32 len - j - 1)) /\
      (!j : int.
         (0 : int) <= j /\
         j < peek_uint32 len - peek_uint32 i ==>
         word_bit (peek_int_to_num j) retval = F) /\
      (!j : int.
         peek_uint32 len <= j /\ j < (64 : int) ==>
         word_bit (peek_int_to_num j) retval = F)`;

val peek_update_def = Define `
  peek_update
    (addr : word8 list)
    (start : word32)
    (lstart : word32)
    (i : word32)
    (retval : word64)
    (o1 : word64) <=>
      (!i1 : int.
         (((0 : int) <= i1 /\ i1 < (64 : int)) /\
          ~(i1 = (63 : int) - peek_uint32 (lstart + i))) ==>
         word_bit (peek_int_to_num i1) o1 =
           word_bit (peek_int_to_num i1) retval) /\
      nth8_stream addr (peek_uint32 (start + i)) =
        word_bit
          (peek_int_to_num
             ((63 : int) - peek_uint32 (lstart + i)))
          o1`;

val peek_final_def = Define `
  peek_final
    (addr : word8 list)
    (start : word32)
    (len : word32)
    (retval : word64) <=>
      (peek_addr_bits addr <
         peek_uint32 start + peek_uint32 len ==>
       retval = (0w : word64)) /\
      (peek_uint32 start + peek_uint32 len <=
         peek_addr_bits addr ==>
       (!i1 : int.
          (0 : int) <= i1 /\ i1 < peek_uint32 len ==>
          word_bit (peek_int_to_num i1) retval =
            nth8_stream addr
              (peek_uint32 start + peek_uint32 len - i1 - 1)) /\
       (!i1 : int.
          peek_uint32 len <= i1 /\ i1 < (64 : int) ==>
          word_bit (peek_int_to_num i1) retval = F))`;

val peek_loop_step_def = Define `
  peek_loop_step
    (addr : word8 list)
    (start : word32)
    (len : word32)
    (lstart : word32)
    (i : word32)
    (retval : word64) <=>
      if i <+ len then
        peek_overflow32 start i /\
        (peek_no_wrap32 start i ==>
         (peek_addr_bits addr < (4294967296 : int) /\
          peek_uint32 (start + i) < peek_addr_bits addr) /\
         peek_overflow32 lstart i /\
         (peek_no_wrap32 lstart i ==>
          peek_uint32 (lstart + i) < (64 : int) /\
          !o1 : word64.
            peek_update addr start lstart i retval o1 ==>
            peek_overflow32 i (1w : word32) /\
            (peek_no_wrap32 i (1w : word32) ==>
             ((0 : int) <=
                peek_uint32 len - peek_uint32 i /\
              peek_uint32 len -
                  peek_uint32 (i + (1w : word32)) <
                peek_uint32 len - peek_uint32 i) /\
             peek_inv
               addr start len (i + (1w : word32)) o1)))
      else
        peek_final addr start len retval`;

val bitwalker_Bitwalker_peek_vc =
  ``!len start : word32.
    !addr : word8 list.
      peek_uint32 len <= (64 : int) ==>
      peek_uint32 start + peek_uint32 len < (4294967296 : int) ==>
      peek_addr_bits addr < (4294967296 : int) ==>
      peek_overflow32 start len /\
      (peek_no_wrap32 start len ==>
       if peek_addr_bits addr < peek_uint32 (start + len) then
         peek_uint32 start + peek_uint32 len <=
           peek_addr_bits addr ==>
         (!i : int.
            (0 : int) <= i /\ i < peek_uint32 len ==>
            word_bit (peek_int_to_num i) (0w : word64) =
              nth8_stream addr
                (peek_uint32 start + peek_uint32 len - i - 1)) /\
         (!i : int.
            peek_uint32 len <= i /\ i < (64 : int) ==>
            word_bit (peek_int_to_num i) (0w : word64) = F)
       else
         (peek_uint32 len <= (64 : int) \/
          w2n len <= w2n (64w : word32)) /\
         (let lstart : word32 = (64w : word32) - len in
            peek_uint32 lstart =
                (64 : int) - peek_uint32 len ==>
            peek_inv
              addr start len (0w : word32) (0w : word64) /\
            !i : word32.
            !retval : word64.
              peek_inv addr start len i retval ==>
              peek_loop_step
                addr start len lstart i retval))``;
