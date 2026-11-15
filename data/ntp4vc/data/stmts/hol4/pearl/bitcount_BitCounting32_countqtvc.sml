(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitcount_BitCounting32_countqtvc: a 32-bit SWAR bit-counting
  verification condition recording five word-level computation steps and the
  generated postcondition implication for the set-bit count. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory pred_setTheory wordsTheory;

val bitcount32_step0_def = Define `
  bitcount32_step0 (n : word32) (x1 : word32) <=>
    x1 = n - ((n >>> 1) && (1431655765w : word32))`;

val bitcount32_step1_def = Define `
  bitcount32_step1 (x1 : word32) (x2 : word32) <=>
    x2 =
      (x1 && (858993459w : word32)) +
      ((x1 >>> 2) && (858993459w : word32))`;

val bitcount32_step2_def = Define `
  bitcount32_step2 (x2 : word32) (x3 : word32) <=>
    x3 =
      (x2 + (x2 >>> 4)) &&
      (252645135w : word32)`;

val bitcount32_step3_def = Define `
  bitcount32_step3 (x3 : word32) (x4 : word32) <=>
    x4 = x3 + (x3 >>> 8)`;

val bitcount32_step4_def = Define `
  bitcount32_step4 (x4 : word32) (x5 : word32) <=>
    x5 = x4 + (x4 >>> 16)`;

val bitcount32_count_logic_def = Define `
  (bitcount32_count_logic (n : word32) : int) =
    &(CARD {i : num | i < 32 /\ word_bit i n})`;

val bitcount_BitCounting32_count_vc =
  ``!n : word32.
      let x1 =
        n - ((n >>> 1) && (1431655765w : word32))
      in
      let x2 =
        (x1 && (858993459w : word32)) +
        ((x1 >>> 2) && (858993459w : word32))
      in
      let x3 =
        (x2 + (x2 >>> 4)) &&
        (252645135w : word32)
      in
      let x4 = x3 + (x3 >>> 8)
      in
      let x5 = x4 + (x4 >>> 16)
      in
      let result = x5 && (63w : word32)
      in
        bitcount32_step0 n x1 /\
        bitcount32_step1 x1 x2 /\
        bitcount32_step2 x2 x3 /\
        bitcount32_step3 x3 x4 /\
        bitcount32_step4 x4 x5 /\
        (&(w2n result) = bitcount32_count_logic n ==>
         &(w2n result) = bitcount32_count_logic n)``;
