(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitcount_AsciiCode_asciiqtvc: a 32-bit ASCII-code verification
  condition relating bit count parity, insertion of a high parity bit, and
  preservation of the lower 31 bits. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory pred_setTheory wordsTheory;

val bit_count32_def = Define `
  bit_count32 (b : word32) =
    CARD {i : num | i < 32 /\ word_bit i b}`;

val valid_ascii32_def = Define `
  valid_ascii32 (b : word32) <=> EVEN (bit_count32 b)`;

val eq_sub32_def = Define `
  eq_sub32 (x : word32) (y : word32) (start : num) (len : num) <=>
    !k : num.
      k < len ==>
      (word_bit (start + k) x = word_bit (start + k) y)`;

val ascii_vc =
  ``!b c : word32.
      ~word_bit (w2n ((32w : word32) - 1w)) b ==>
      w2n c = bit_count32 b ==>
      (((31w : word32) <+ (32w : word32)) \/ (31 : int) < 32) /\
      (let maskbit : word32 = c << w2n (31w : word32)
       in
         maskbit = c << 31 ==>
         (let code : word32 = b || maskbit
          in
            eq_sub32
              code b
              (w2n (0w : word32))
              (w2n ((32w : word32) - 1w)) /\
            valid_ascii32 code))``;
