(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_wmpn_sub_nqtvc: the loop verification
  condition for equal-length multiprecision subtraction with pointer
  aliasing, borrow arithmetic, memory updates, and frame preservation.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

Datatype:
  mpsubwn_ptr =
    MpSubWnPtr (word64 list) int int int bool 'zone
End

val mpsubwn_data_def = Define `
  mpsubwn_data
      (MpSubWnPtr data offset minimum maximum writable zone) =
    data`;

val mpsubwn_offset_def = Define `
  mpsubwn_offset
      (MpSubWnPtr data offset minimum maximum writable zone) =
    offset`;

val mpsubwn_minimum_def = Define `
  mpsubwn_minimum
      (MpSubWnPtr data offset minimum maximum writable zone) =
    minimum`;

val mpsubwn_maximum_def = Define `
  mpsubwn_maximum
      (MpSubWnPtr data offset minimum maximum writable zone) =
    maximum`;

val mpsubwn_writable_def = Define `
  mpsubwn_writable
      (MpSubWnPtr data offset minimum maximum writable zone) =
    writable`;

val mpsubwn_zone_def = Define `
  mpsubwn_zone
      (MpSubWnPtr data offset minimum maximum writable zone) =
    zone`;

val mpsubwn_to_num_def = Define `
  mpsubwn_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val mpsubwn_pelts_def = Define `
  mpsubwn_pelts (p : 'zone mpsubwn_ptr) (index : int) =
    if mpsubwn_to_num index < LENGTH (mpsubwn_data p) then
      EL (mpsubwn_to_num index) (mpsubwn_data p)
    else
      (0w : word64)`;

val mpsubwn_plength_def = Define `
  mpsubwn_plength (p : 'zone mpsubwn_ptr) =
    &(LENGTH (mpsubwn_data p))`;

val mpsubwn_int32_in_bounds_def = Define `
  mpsubwn_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val mpsubwn_valid_def = Define `
  mpsubwn_valid (p : 'zone mpsubwn_ptr) (size : int) <=>
    mpsubwn_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= mpsubwn_minimum p /\
     mpsubwn_minimum p <= mpsubwn_offset p) /\
    mpsubwn_offset p + size <= mpsubwn_maximum p /\
    mpsubwn_maximum p <= mpsubwn_plength p`;

val mpsubwn_access_def = Define `
  mpsubwn_access (p : 'zone mpsubwn_ptr) (index : int) <=>
    mpsubwn_minimum p <= index /\
    index < mpsubwn_maximum p`;

val mpsubwn_radix_def = Define `
  mpsubwn_radix = (18446744073709551616 : int)`;

val mpsubwn_radix_power_def = Define `
  mpsubwn_radix_power (exponent : int) =
    mpsubwn_radix ** mpsubwn_to_num exponent`;

val mpsubwn_value_from_def = Define `
  (mpsubwn_value_from
      (p : 'zone mpsubwn_ptr) (index : int) 0 =
     (0 : int)) /\
  (mpsubwn_value_from p index (SUC count) =
     &(w2n (mpsubwn_pelts p index)) +
       mpsubwn_radix *
         mpsubwn_value_from p (index + (1 : int)) count)`;

val mpsubwn_value_def = Define `
  mpsubwn_value (p : 'zone mpsubwn_ptr) (size : int) =
    mpsubwn_value_from
      p (mpsubwn_offset p) (mpsubwn_to_num size)`;

val mpsubwn_same_pelts_def = Define `
  mpsubwn_same_pelts
      (left : 'zone mpsubwn_ptr)
      (right : 'zone mpsubwn_ptr) <=>
    !i : int.
      mpsubwn_pelts left i = mpsubwn_pelts right i`;

val mpsubwn_map_eq_sub_def = Define `
  mpsubwn_map_eq_sub
      (left : 'zone mpsubwn_ptr)
      (right : 'zone mpsubwn_ptr)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      mpsubwn_pelts left i = mpsubwn_pelts right i`;

val mpsubwn_alias_safe_def = Define `
  mpsubwn_alias_safe
      (result : 'zone mpsubwn_ptr)
      (source : 'zone mpsubwn_ptr)
      (size : int) <=>
    mpsubwn_offset result = mpsubwn_offset source \/
    mpsubwn_offset result + size <= mpsubwn_offset source \/
    mpsubwn_offset source + size <= mpsubwn_offset result`;

val mpsubwn_frame_def = Define `
  mpsubwn_frame
      (current : 'zone mpsubwn_ptr)
      (original : 'zone mpsubwn_ptr)
      (size : int) <=>
    !j : int.
      j < mpsubwn_offset current \/
      mpsubwn_offset current + size <= j ==>
      mpsubwn_pelts current j = mpsubwn_pelts original j`;

val mpsubwn_borrow_range_def = Define `
  mpsubwn_borrow_range (borrow : word64) <=>
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int)`;

val mpsubwn_value_equation_def = Define `
  mpsubwn_value_equation
      (current : 'zone mpsubwn_ptr)
      (x : 'zone mpsubwn_ptr)
      (y : 'zone mpsubwn_ptr)
      (size : int)
      (borrow : word64) <=>
    mpsubwn_value current size -
        mpsubwn_radix_power size * &(w2n borrow) =
      mpsubwn_value x size - mpsubwn_value y size`;

val mpsubwn_y_snapshot_def = Define `
  mpsubwn_y_snapshot
      (current_y : 'zone mpsubwn_ptr)
      (current_r : 'zone mpsubwn_ptr)
      (original_y : 'zone mpsubwn_ptr) <=>
    mpsubwn_data current_y = mpsubwn_data current_r /\
    LENGTH (mpsubwn_data current_r) =
      LENGTH (mpsubwn_data original_y) /\
    mpsubwn_offset current_y = mpsubwn_offset original_y /\
    mpsubwn_minimum current_y = mpsubwn_minimum original_y /\
    mpsubwn_maximum current_y = mpsubwn_maximum original_y /\
    mpsubwn_writable current_y = mpsubwn_writable original_y /\
    mpsubwn_zone current_y = mpsubwn_zone original_y`;

val mpsubwn_x_snapshot_def = Define `
  mpsubwn_x_snapshot
      (current_x : 'zone mpsubwn_ptr)
      (current_r : 'zone mpsubwn_ptr)
      (original_x : 'zone mpsubwn_ptr) <=>
    mpsubwn_data current_x = mpsubwn_data current_r /\
    LENGTH (mpsubwn_data current_r) =
      LENGTH (mpsubwn_data original_x) /\
    mpsubwn_offset current_x = mpsubwn_offset original_x /\
    mpsubwn_minimum current_x = mpsubwn_minimum original_x /\
    mpsubwn_maximum current_x = mpsubwn_maximum original_x /\
    mpsubwn_writable current_x = mpsubwn_writable original_x /\
    mpsubwn_zone current_x = mpsubwn_zone original_x`;

val mpsubwn_r_snapshot_def = Define `
  mpsubwn_r_snapshot
      (current_r : 'zone mpsubwn_ptr)
      (original_r : 'zone mpsubwn_ptr) <=>
    LENGTH (mpsubwn_data current_r) =
      LENGTH (mpsubwn_data original_r) /\
    mpsubwn_offset current_r = mpsubwn_offset original_r /\
    mpsubwn_minimum current_r = mpsubwn_minimum original_r /\
    mpsubwn_maximum current_r = mpsubwn_maximum original_r /\
    mpsubwn_writable current_r = mpsubwn_writable original_r /\
    mpsubwn_zone current_r = mpsubwn_zone original_r`;

val mpsubwn_alias_state_def = Define `
  mpsubwn_alias_state
      (current_r : 'zone mpsubwn_ptr)
      (current_source : 'zone mpsubwn_ptr)
      (original_source : 'zone mpsubwn_ptr)
      (size : int) <=>
    mpsubwn_offset current_r = mpsubwn_offset current_source \/
    mpsubwn_map_eq_sub
      current_source original_source
      (mpsubwn_offset current_source)
      (mpsubwn_offset current_source + size)`;

val mpsubwn_loop_invariant_def = Define `
  mpsubwn_loop_invariant
      (original_r : 'zone mpsubwn_ptr)
      (original_x : 'zone mpsubwn_ptr)
      (original_y : 'zone mpsubwn_ptr)
      (size : word32)
      (index : word32)
      (borrow : word64)
      (current_y : 'zone mpsubwn_ptr)
      (current_x : 'zone mpsubwn_ptr)
      (current_r : 'zone mpsubwn_ptr) <=>
    ((0 : int) <= w2i index /\ w2i index <= w2i size) /\
    mpsubwn_value_equation
      current_r original_x original_y (w2i index) borrow /\
    mpsubwn_frame current_r original_r (w2i index) /\
    (mpsubwn_same_pelts current_x current_r /\
     mpsubwn_same_pelts current_r current_y) /\
    mpsubwn_alias_state
      current_r current_x original_x (w2i size) /\
    mpsubwn_alias_state
      current_r current_y original_y (w2i size) /\
    mpsubwn_borrow_range borrow`;

val mpsubwn_write_relation_def = Define `
  mpsubwn_write_relation
      (updated : 'zone mpsubwn_ptr)
      (previous : 'zone mpsubwn_ptr)
      (index : int)
      (result : word64) <=>
    (!j : int.
       mpsubwn_pelts updated j =
         if j = index then result else mpsubwn_pelts previous j) /\
    mpsubwn_pelts updated index = result`;

val mpsubwn_after_write_def = Define `
  mpsubwn_after_write
      (original_r : 'zone mpsubwn_ptr)
      (original_x : 'zone mpsubwn_ptr)
      (original_y : 'zone mpsubwn_ptr)
      (size : word32)
      (index : word32)
      (borrow : word64)
      (updated_y : 'zone mpsubwn_ptr)
      (updated_x : 'zone mpsubwn_ptr)
      (updated_r : 'zone mpsubwn_ptr) <=>
    mpsubwn_int32_in_bounds (w2i index + (1 : int)) /\
    (!next : word32.
       w2i next = w2i index + (1 : int) ==>
       ((0 : int) <= w2i size - w2i index /\
        w2i size - w2i next < w2i size - w2i index) /\
       mpsubwn_loop_invariant
         original_r original_x original_y size next borrow
         updated_y updated_x updated_r)`;

val mpsubwn_subtraction_step_def = Define `
  mpsubwn_subtraction_step
      (original_r : 'zone mpsubwn_ptr)
      (original_x : 'zone mpsubwn_ptr)
      (original_y : 'zone mpsubwn_ptr)
      (size : word32)
      (index : word32)
      (borrow_in : word64)
      (current_y : 'zone mpsubwn_ptr)
      (current_x : 'zone mpsubwn_ptr)
      (current_r : 'zone mpsubwn_ptr) <=>
    mpsubwn_access
      current_x (mpsubwn_offset current_x + w2i index) /\
    mpsubwn_access
      current_y (mpsubwn_offset current_y + w2i index) /\
    mpsubwn_access
      original_x (mpsubwn_offset original_x + w2i index) /\
    mpsubwn_access
      original_y (mpsubwn_offset original_y + w2i index) /\
    mpsubwn_borrow_range borrow_in /\
    (!result borrow_out : word64.
       (&(w2n result) -
          mpsubwn_radix * &(w2n borrow_out) =
        &(w2n
            (mpsubwn_pelts
              current_x (mpsubwn_offset current_x + w2i index))) -
          &(w2n
            (mpsubwn_pelts
              current_y (mpsubwn_offset current_y + w2i index))) -
          &(w2n borrow_in)) /\
       mpsubwn_borrow_range borrow_out ==>
       (mpsubwn_access
          current_r (mpsubwn_offset current_r + w2i index) /\
        mpsubwn_writable current_r = T) /\
       (!updated_y updated_x updated_r : 'zone mpsubwn_ptr.
          mpsubwn_y_snapshot updated_y updated_r current_y ==>
          mpsubwn_x_snapshot updated_x updated_r current_x ==>
          mpsubwn_r_snapshot updated_r current_r ==>
          mpsubwn_write_relation
            updated_r current_r
            (mpsubwn_offset updated_r + w2i index) result ==>
          mpsubwn_after_write
            original_r original_x original_y size index borrow_out
            updated_y updated_x updated_r))`;

val mpsubwn_final_state_def = Define `
  mpsubwn_final_state
      (original_r : 'zone mpsubwn_ptr)
      (original_x : 'zone mpsubwn_ptr)
      (original_y : 'zone mpsubwn_ptr)
      (size : word32)
      (borrow : word64)
      (current_y : 'zone mpsubwn_ptr)
      (current_x : 'zone mpsubwn_ptr)
      (current_r : 'zone mpsubwn_ptr) <=>
    mpsubwn_value_equation
      current_r original_x original_y (w2i size) borrow /\
    mpsubwn_borrow_range borrow /\
    mpsubwn_frame current_r original_r (w2i size) /\
    mpsubwn_alias_state
      current_r current_x original_x (w2i size) /\
    mpsubwn_alias_state
      current_r current_y original_y (w2i size)`;

val mpsubwn_loop_step_def = Define `
  mpsubwn_loop_step
      (original_r : 'zone mpsubwn_ptr)
      (original_x : 'zone mpsubwn_ptr)
      (original_y : 'zone mpsubwn_ptr)
      (size : word32)
      (index : word32)
      (borrow : word64)
      (current_y : 'zone mpsubwn_ptr)
      (current_x : 'zone mpsubwn_ptr)
      (current_r : 'zone mpsubwn_ptr) <=>
    if w2i index < w2i size then
      mpsubwn_subtraction_step
        original_r original_x original_y size index borrow
        current_y current_x current_r
    else
      mpsubwn_final_state
        original_r original_x original_y size borrow
        current_y current_x current_r`;

val sub_Sub_wmpn_sub_n_vc =
  ``!size : word32.
    !r x y : 'zone mpsubwn_ptr.
      (0 : int) <= w2i size ==>
      mpsubwn_valid r (w2i size) ==>
      mpsubwn_valid x (w2i size) ==>
      mpsubwn_valid y (w2i size) ==>
      mpsubwn_alias_safe r x (w2i size) ==>
      mpsubwn_alias_safe r y (w2i size) ==>
      mpsubwn_data r = mpsubwn_data x ==>
      mpsubwn_data x = mpsubwn_data y ==>
      mpsubwn_writable r = T ==>
      ((0 : int) <= (0 : int)) /\
      ((0 : int) <= w2i size) /\
      (mpsubwn_value r (0 : int) -
         mpsubwn_radix_power (0 : int) * (0 : int) =
       mpsubwn_value x (0 : int) -
         mpsubwn_value y (0 : int)) /\
      mpsubwn_same_pelts x r /\
      mpsubwn_same_pelts r y /\
      (mpsubwn_offset r = mpsubwn_offset x \/
       mpsubwn_map_eq_sub
         x x (mpsubwn_offset x)
         (mpsubwn_offset x + w2i size)) /\
      (mpsubwn_offset r = mpsubwn_offset y \/
       mpsubwn_map_eq_sub
         y y (mpsubwn_offset y)
         (mpsubwn_offset y + w2i size)) /\
      ((0 : int) <= (0 : int)) /\
      ((0 : int) <= (1 : int)) /\
      (!index : word32.
       !borrow : word64.
       !current_y current_x current_r : 'zone mpsubwn_ptr.
         mpsubwn_y_snapshot current_y current_r y ==>
         mpsubwn_x_snapshot current_x current_r x ==>
         mpsubwn_r_snapshot current_r r ==>
         mpsubwn_loop_invariant
           r x y size index borrow current_y current_x current_r ==>
         mpsubwn_loop_step
           r x y size index borrow current_y current_x current_r)``;
