(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/queens_bv_Bits_belowqtvc: a 32-bit low-bit mask represents exactly
  the finite integer interval from zero to the unsigned mask width.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory pred_setTheory wordsTheory;

val queens_bv_int_to_num_def = Define `
  queens_bv_int_to_num (z : int) =
    if z < 0 then 0 else Num z`;

val queens_bv_interval_def = Define `
  queens_bv_interval (u : int) =
    {i : int | (0 : int) <= i /\ i < u}`;

val queens_bv_bits_invariant_def = Define `
  queens_bv_bits_invariant (bits : word32) (model : int set) <=>
    !i : int.
      ((((0 : int) <= i /\ i < (32 : int)) /\
        word_bit (queens_bv_int_to_num i) bits) <=>
       i IN model)`;

val queens_bv_Bits_belowqtvc_statement =
  ``!bv : 'state -> word32.
    !mdl : 'state -> int set.
      ((!self : 'state.
          FINITE (mdl self) /\
          queens_bv_bits_invariant (bv self) (mdl self)) /\
       (!a b : 'state.
          bv a = bv b /\ mdl a = mdl b ==> a = b))
      ==>
      !n : word32.
        n <=+ (32w : word32) ==>
        let o1 = queens_bv_interval (&(w2n n)) in
        let o2 : word32 =
          ~((4294967295w : word32) << w2n n)
        in
          queens_bv_bits_invariant o2 o1 /\
          !result : 'state.
            bv result = o2 /\ mdl result = o1 ==>
            mdl result = queens_bv_interval (&(w2n n))``;
