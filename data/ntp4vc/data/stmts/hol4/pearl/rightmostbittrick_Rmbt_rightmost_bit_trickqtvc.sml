(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/rightmostbittrick_Rmbt_rightmost_bit_trickqtvc: the 64-bit
  rightmost-bit trick, where x AND -x isolates a set bit whose lower bits
  are zero and clears every other bit. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory wordsTheory;

val rmbt_eq_sub64_def = Define `
  rmbt_eq_sub64
    (a : word64) (b : word64) (start : num) (len : num) <=>
    !k : num.
      k < len ==>
      (word_bit (start + k) a = word_bit (start + k) b)`;

val rightmostbittrick_Rmbt_rightmost_bit_trick_vc =
  ``!x : word64.
      ~(x = (0w : word64)) ==>
      ~(x = (0w : word64)) /\
      !p_bv : word64.
        p_bv <+ (64w : word64) /\
        rmbt_eq_sub64 x (0w : word64) 0 (w2n p_bv) /\
        word_bit (w2n p_bv) x
        ==>
        let r : word64 = x && -x
        in
          ((0 : int) <= &(w2n p_bv) /\
           &(w2n p_bv) < (64 : int)) /\
          rmbt_eq_sub64 x (0w : word64) 0 (w2n p_bv) /\
          word_bit (w2n p_bv) x /\
          rmbt_eq_sub64 r (0w : word64) 0 (w2n p_bv) /\
          rmbt_eq_sub64
            r (0w : word64)
            (w2n p_bv + 1)
            (63 - w2n p_bv) /\
          word_bit (w2n p_bv) r``;
