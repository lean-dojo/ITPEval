(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div3by2_invqtvc: the verification condition
  for reciprocal-based division of a three-limb unsigned integer by a
  normalized two-limb 64-bit divisor, including quotient corrections and
  the final two-limb remainder bound. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory wordsTheory;

val div3by2_inv_radix_def = Define `
  div3by2_inv_radix = (18446744073709551616 : int)`;

val div3by2_inv_uint_def = Define `
  div3by2_inv_uint (x : word64) = &(w2n x)`;

val div3by2_inv_carry_bounds_def = Define `
  div3by2_inv_carry_bounds (c : word64) <=>
    (0 : int) <= div3by2_inv_uint c /\
    div3by2_inv_uint c <= (1 : int)`;

val div3by2_inv_trivial_bounds_def = Define `
  div3by2_inv_trivial_bounds <=>
    (0 : int) <= (0 : int) /\ (0 : int) <= (1 : int)`;

val div3by2_inv_reciprocal_3by2_def = Define `
  div3by2_inv_reciprocal_3by2
      (v : word64) (dh : word64) (dl : word64) <=>
    div3by2_inv_uint v =
      (div3by2_inv_radix * div3by2_inv_radix *
         div3by2_inv_radix - (1 : int)) /
        (div3by2_inv_uint dl +
         div3by2_inv_radix * div3by2_inv_uint dh) -
      div3by2_inv_radix`;

val div3by2_inv_result_def = Define `
  div3by2_inv_result
      (q : word64) (rl : word64) (rh : word64)
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64) <=>
    div3by2_inv_uint q * div3by2_inv_uint dl +
        div3by2_inv_radix * div3by2_inv_uint q *
          div3by2_inv_uint dh +
        div3by2_inv_uint rl +
        div3by2_inv_radix * div3by2_inv_uint rh =
      div3by2_inv_uint ul +
        div3by2_inv_radix * div3by2_inv_uint um +
        div3by2_inv_radix * div3by2_inv_radix *
          div3by2_inv_uint uh /\
    (0 : int) <=
      div3by2_inv_uint rl +
        div3by2_inv_radix * div3by2_inv_uint rh /\
    div3by2_inv_uint rl +
        div3by2_inv_radix * div3by2_inv_uint rh <
      div3by2_inv_uint dl +
        div3by2_inv_radix * div3by2_inv_uint dh`;

val div3by2_inv_first_quotient_after_increment_def = Define `
  div3by2_inv_first_quotient_after_increment
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o3 : word64) (bl1 : word64) (bh1 : word64) <=>
    !o5 : word64.
      div3by2_inv_uint o5 =
        (div3by2_inv_uint o3 + (1 : int)) %
          div3by2_inv_radix
      ==>
      div3by2_inv_result o5 bl1 bh1 dl dh ul um uh`;

val div3by2_inv_first_high_subtraction_def = Define `
  div3by2_inv_first_high_subtraction
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o3 : word64) (rh : word64)
      (bl1 : word64) (b1 : word64) <=>
    !bh1 bprime : word64.
      div3by2_inv_uint bh1 -
          div3by2_inv_radix * div3by2_inv_uint bprime =
        div3by2_inv_uint rh - div3by2_inv_uint dh -
          div3by2_inv_uint b1 /\
      div3by2_inv_carry_bounds bprime
      ==>
      div3by2_inv_first_quotient_after_increment
        dl dh ul um uh o3 bl1 bh1`;

val div3by2_inv_first_low_subtraction_def = Define `
  div3by2_inv_first_low_subtraction
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o3 : word64) (rl : word64) (rh : word64) <=>
    !bl1 b1 : word64.
      div3by2_inv_uint bl1 -
          div3by2_inv_radix * div3by2_inv_uint b1 =
        div3by2_inv_uint rl - div3by2_inv_uint dl - (0 : int) /\
      div3by2_inv_carry_bounds b1
      ==>
      div3by2_inv_carry_bounds b1 /\
      div3by2_inv_first_high_subtraction
        dl dh ul um uh o3 rh bl1 b1`;

val div3by2_inv_first_flag_premise_def = Define `
  div3by2_inv_first_flag_premise
      (dh : word64) (dl : word64)
      (rh : word64) (rl : word64) (decision : bool) <=>
    if div3by2_inv_uint dh < div3by2_inv_uint rh then
      decision = T
    else
      ?equal_flag : bool.
        ((div3by2_inv_uint rh = div3by2_inv_uint dh ==>
            equal_flag = T) /\
         (equal_flag = T ==> rh = dh)) /\
        decision =
          (if equal_flag = T then
             if div3by2_inv_uint dl <= div3by2_inv_uint rl
             then T
             else F
           else F)`;

val div3by2_inv_first_flag_obligation_def = Define `
  div3by2_inv_first_flag_obligation
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o3 : word64) (rl : word64) (rh : word64) <=>
    !decision : bool.
      div3by2_inv_first_flag_premise dh dl rh rl decision
      ==>
      if decision = T then
        div3by2_inv_trivial_bounds /\
        div3by2_inv_first_low_subtraction
          dl dh ul um uh o3 rl rh
      else
        div3by2_inv_result o3 rl rh dl dh ul um uh`;

val div3by2_inv_first_high_addition_def = Define `
  div3by2_inv_first_high_addition
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o3 : word64) (bh : word64)
      (rl : word64) (c1 : word64) <=>
    !rh cprime : word64.
      div3by2_inv_uint rh +
          div3by2_inv_radix * div3by2_inv_uint cprime =
        div3by2_inv_uint bh + div3by2_inv_uint dh +
          div3by2_inv_uint c1 /\
      div3by2_inv_carry_bounds cprime
      ==>
      div3by2_inv_first_flag_obligation
        dl dh ul um uh o3 rl rh`;

val div3by2_inv_first_low_addition_def = Define `
  div3by2_inv_first_low_addition
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o3 : word64) (bl : word64) (bh : word64) <=>
    !rl c1 : word64.
      div3by2_inv_uint rl +
          div3by2_inv_radix * div3by2_inv_uint c1 =
        div3by2_inv_uint bl + div3by2_inv_uint dl + (0 : int) /\
      div3by2_inv_carry_bounds c1
      ==>
      div3by2_inv_carry_bounds c1 /\
      div3by2_inv_first_high_addition
        dl dh ul um uh o3 bh rl c1`;

val div3by2_inv_first_correction_def = Define `
  div3by2_inv_first_correction
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o1 : word64) (bl : word64) (bh : word64) <=>
    !o3 : word64.
      div3by2_inv_uint o3 =
        (div3by2_inv_uint o1 - (1 : int)) %
          div3by2_inv_radix
      ==>
      div3by2_inv_trivial_bounds /\
      div3by2_inv_first_low_addition
        dl dh ul um uh o3 bl bh`;

val div3by2_inv_second_quotient_after_increment_def = Define `
  div3by2_inv_second_quotient_after_increment
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o1 : word64) (bl1 : word64) (bh1 : word64) <=>
    !o4 : word64.
      div3by2_inv_uint o4 =
        (div3by2_inv_uint o1 + (1 : int)) %
          div3by2_inv_radix
      ==>
      div3by2_inv_result o4 bl1 bh1 dl dh ul um uh`;

val div3by2_inv_second_high_subtraction_def = Define `
  div3by2_inv_second_high_subtraction
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o1 : word64) (bh : word64)
      (bl1 : word64) (b3 : word64) <=>
    !bh1 bprime : word64.
      div3by2_inv_uint bh1 -
          div3by2_inv_radix * div3by2_inv_uint bprime =
        div3by2_inv_uint bh - div3by2_inv_uint dh -
          div3by2_inv_uint b3 /\
      div3by2_inv_carry_bounds bprime
      ==>
      div3by2_inv_second_quotient_after_increment
        dl dh ul um uh o1 bl1 bh1`;

val div3by2_inv_second_low_subtraction_def = Define `
  div3by2_inv_second_low_subtraction
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o1 : word64) (bl : word64) (bh : word64) <=>
    !bl1 b3 : word64.
      div3by2_inv_uint bl1 -
          div3by2_inv_radix * div3by2_inv_uint b3 =
        div3by2_inv_uint bl - div3by2_inv_uint dl - (0 : int) /\
      div3by2_inv_carry_bounds b3
      ==>
      div3by2_inv_carry_bounds b3 /\
      div3by2_inv_second_high_subtraction
        dl dh ul um uh o1 bh bl1 b3`;

val div3by2_inv_second_flag_premise_def = Define `
  div3by2_inv_second_flag_premise
      (dh : word64) (dl : word64)
      (bh : word64) (bl : word64) (decision : bool) <=>
    if div3by2_inv_uint dh < div3by2_inv_uint bh then
      decision = T
    else
      ?equal_flag : bool.
        ((div3by2_inv_uint bh = div3by2_inv_uint dh ==>
            equal_flag = T) /\
         (equal_flag = T ==> bh = dh)) /\
        decision =
          (if equal_flag = T then
             if div3by2_inv_uint dl <= div3by2_inv_uint bl
             then T
             else F
           else F)`;

val div3by2_inv_second_flag_obligation_def = Define `
  div3by2_inv_second_flag_obligation
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (o1 : word64) (bl : word64) (bh : word64) <=>
    !decision : bool.
      div3by2_inv_second_flag_premise dh dl bh bl decision
      ==>
      if decision = T then
        div3by2_inv_trivial_bounds /\
        div3by2_inv_second_low_subtraction
          dl dh ul um uh o1 bl bh
      else
        div3by2_inv_result o1 bl bh dl dh ul um uh`;

val div3by2_inv_correction_branches_def = Define `
  div3by2_inv_correction_branches
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (o1 : word64)
      (bl : word64) (bh : word64) <=>
    if div3by2_inv_uint sl <= div3by2_inv_uint bh then
      div3by2_inv_first_correction
        dl dh ul um uh o1 bl bh
    else
      div3by2_inv_second_flag_obligation
        dl dh ul um uh o1 bl bh`;

val div3by2_inv_after_second_high_borrow_def = Define `
  div3by2_inv_after_second_high_borrow
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (o1 : word64)
      (ih : word64) (bl : word64) (b2 : word64) <=>
    !bh b2prime : word64.
      div3by2_inv_uint bh -
          div3by2_inv_radix * div3by2_inv_uint b2prime =
        div3by2_inv_uint ih - div3by2_inv_uint dh -
          div3by2_inv_uint b2 /\
      div3by2_inv_carry_bounds b2prime
      ==>
      div3by2_inv_correction_branches
        dl dh ul um uh sl o1 bl bh`;

val div3by2_inv_after_second_low_borrow_def = Define `
  div3by2_inv_after_second_low_borrow
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (o1 : word64)
      (il : word64) (ih : word64) <=>
    !bl b2 : word64.
      div3by2_inv_uint bl -
          div3by2_inv_radix * div3by2_inv_uint b2 =
        div3by2_inv_uint il - div3by2_inv_uint dl - (0 : int) /\
      div3by2_inv_carry_bounds b2
      ==>
      div3by2_inv_carry_bounds b2 /\
      div3by2_inv_after_second_high_borrow
        dl dh ul um uh sl o1 ih bl b2`;

val div3by2_inv_after_first_high_borrow_def = Define `
  div3by2_inv_after_first_high_borrow
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (o1 : word64) (o2 : word64)
      (th : word64) (il : word64) (b : word64) <=>
    !ih bprime : word64.
      div3by2_inv_uint ih -
          div3by2_inv_radix * div3by2_inv_uint bprime =
        div3by2_inv_uint o2 - div3by2_inv_uint th -
          div3by2_inv_uint b /\
      div3by2_inv_carry_bounds bprime
      ==>
      div3by2_inv_trivial_bounds /\
      div3by2_inv_after_second_low_borrow
        dl dh ul um uh sl o1 il ih`;

val div3by2_inv_after_first_low_borrow_def = Define `
  div3by2_inv_after_first_low_borrow
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (o1 : word64) (o2 : word64)
      (tl : word64) (th : word64) <=>
    !il b : word64.
      div3by2_inv_uint il -
          div3by2_inv_radix * div3by2_inv_uint b =
        div3by2_inv_uint ul - div3by2_inv_uint tl - (0 : int) /\
      div3by2_inv_carry_bounds b
      ==>
      div3by2_inv_carry_bounds b /\
      div3by2_inv_after_first_high_borrow
        dl dh ul um uh sl o1 o2 th il b`;

val div3by2_inv_after_low_product_def = Define `
  div3by2_inv_after_low_product
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (sh : word64)
      (o1 : word64) (o2 : word64) <=>
    !tl th : word64.
      div3by2_inv_uint tl +
          div3by2_inv_radix * div3by2_inv_uint th =
        div3by2_inv_uint sh * div3by2_inv_uint dl
      ==>
      div3by2_inv_trivial_bounds /\
      div3by2_inv_after_first_low_borrow
        dl dh ul um uh sl o1 o2 tl th`;

val div3by2_inv_after_o2_def = Define `
  div3by2_inv_after_o2
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (sh : word64)
      (o1 : word64) (p : word64) <=>
    !o2 : word64.
      div3by2_inv_uint o2 =
        (div3by2_inv_uint um - div3by2_inv_uint p) %
          div3by2_inv_radix
      ==>
      ~(div3by2_inv_radix = (0 : int)) /\
      div3by2_inv_after_low_product
        dl dh ul um uh sl sh o1 o2`;

val div3by2_inv_after_p_def = Define `
  div3by2_inv_after_p
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (sh : word64) (o1 : word64) <=>
    !p : word64.
      div3by2_inv_uint p =
        (div3by2_inv_uint dh * div3by2_inv_uint sh) %
          div3by2_inv_radix
      ==>
      div3by2_inv_after_o2
        dl dh ul um uh sl sh o1 p`;

val div3by2_inv_after_o1_def = Define `
  div3by2_inv_after_o1
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (sl : word64) (sh : word64) <=>
    !o1 : word64.
      div3by2_inv_uint o1 =
        (div3by2_inv_uint sh + (1 : int)) %
          div3by2_inv_radix
      ==>
      div3by2_inv_after_p
        dl dh ul um uh sl sh o1`;

val div3by2_inv_high_add_obligation_def = Define `
  div3by2_inv_high_add_obligation
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (h : word64) (sl : word64) (c : word64) <=>
    !sh cprime : word64.
      div3by2_inv_uint sh +
          div3by2_inv_radix * div3by2_inv_uint cprime =
        div3by2_inv_uint uh + div3by2_inv_uint h +
          div3by2_inv_uint c /\
      div3by2_inv_carry_bounds cprime
      ==>
      div3by2_inv_after_o1
        dl dh ul um uh sl sh`;

val div3by2_inv_low_add_obligation_def = Define `
  div3by2_inv_low_add_obligation
      (dl : word64) (dh : word64)
      (ul : word64) (um : word64) (uh : word64)
      (l : word64) (h : word64) <=>
    !sl c : word64.
      div3by2_inv_uint sl +
          div3by2_inv_radix * div3by2_inv_uint c =
        div3by2_inv_uint um + div3by2_inv_uint l + (0 : int) /\
      div3by2_inv_carry_bounds c
      ==>
      div3by2_inv_carry_bounds c /\
      div3by2_inv_high_add_obligation
        dl dh ul um uh h sl c`;

val div_Div_div3by2_invqtvc_statement =
  ``!dh v dl um uh l h ul : word64.
      div3by2_inv_radix / (2 : int) <= div3by2_inv_uint dh
      ==>
      div3by2_inv_reciprocal_3by2 v dh dl
      ==>
      div3by2_inv_uint um +
          div3by2_inv_radix * div3by2_inv_uint uh <
        div3by2_inv_uint dl +
          div3by2_inv_radix * div3by2_inv_uint dh
      ==>
      div3by2_inv_uint l +
          div3by2_inv_radix * div3by2_inv_uint h =
        div3by2_inv_uint v * div3by2_inv_uint uh
      ==>
      (0 : int) <= (0 : int) /\
      (0 : int) <= (1 : int) /\
      div3by2_inv_low_add_obligation dl dh ul um uh l h``;
