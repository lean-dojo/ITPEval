(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/bitcount_Hamming_hammingDqtvc: the Hamming distance between two
  32-bit words equals the population count of their bitwise XOR. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory pred_setTheory wordsTheory;

val bitcount32_count_logic_def = Define `
  (bitcount32_count_logic (n : word32) : int) =
    &(CARD {i : num | i < 32 /\ word_bit i n})`;

val hamming_distance_logic_def = Define `
  (hamming_distance_logic (a : word32) (b : word32) : int) =
    &(CARD
        {i : num |
           i < 32 /\ ~(word_bit i a = word_bit i b)})`;

val bitcount_Hamming_hammingD_vc =
  ``!result a b : word32.
      &(w2n result) = bitcount32_count_logic (a ?? b)
      ==>
      &(w2n result) = hamming_distance_logic a b``;
