(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/queens_bv_Bits_rightmost_bit_trickqtvc: a nonzero 32-bit word
  AND its two's-complement negation represents exactly the singleton
  containing its least set-bit index. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory pred_setTheory wordsTheory;

val queens_bv_rightmost_int_to_num_def = Define `
  queens_bv_rightmost_int_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val queens_bv_rightmost_minimum_def = Define `
  queens_bv_rightmost_minimum (s : int set) =
    @m : int. m IN s /\ !j : int. j IN s ==> m <= j`;

val queens_bv_rightmost_invariant_def = Define `
  queens_bv_rightmost_invariant
      (bits : word32) (model : int set) <=>
    !i : int.
      ((((0 : int) <= i /\ i < (32 : int)) /\
        word_bit (queens_bv_rightmost_int_to_num i) bits) <=>
       i IN model)`;

val queens_bv_Bits_rightmost_bit_trickqtvc_statement =
  ``!bv : 'state -> word32.
    !mdl : 'state -> int set.
      ((!self : 'state.
          FINITE (mdl self) /\
          queens_bv_rightmost_invariant (bv self) (mdl self)) /\
       (!a b : 'state.
          bv a = bv b /\ mdl a = mdl b ==> a = b))
      ==>
      !a : 'state.
        ~(mdl a = {}) ==>
        let res : word32 =
          bv a && word_2comp (bv a)
        in
        let o1 : int set =
          {queens_bv_rightmost_minimum (mdl a)}
        in
          queens_bv_rightmost_invariant res o1 /\
          !result : 'state.
            bv result = res /\ mdl result = o1 ==>
            mdl result =
              {queens_bv_rightmost_minimum (mdl a)}``;
