(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_Add_wmpn_addqtvc: the verification condition for
  unequal-length multiprecision addition, including initial limb addition,
  carry propagation, copying remaining limbs, pointer aliasing, map updates,
  and memory framing. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val wmpnadd_radix_def = Define `
  wmpnadd_radix = (18446744073709551616 : int)`;

val wmpnadd_to_num_def = Define `
  wmpnadd_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val wmpnadd_int32_in_bounds_def = Define `
  wmpnadd_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val wmpnadd_radix_power_def = Define `
  wmpnadd_radix_power (n : int) =
    wmpnadd_radix ** wmpnadd_to_num n`;

val wmpnadd_value_from_def = Define `
  (wmpnadd_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (wmpnadd_value_from pelts p index (SUC count) =
     &(w2n (pelts p index)) +
       wmpnadd_radix *
         wmpnadd_value_from pelts p (index + (1 : int)) count)`;

val wmpnadd_value_def = Define `
  wmpnadd_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    wmpnadd_value_from pelts p (offset p) (wmpnadd_to_num count)`;

val wmpnadd_valid_def = Define `
  wmpnadd_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    wmpnadd_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val wmpnadd_same_data_def = Define `
  wmpnadd_same_data
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    pelts left = pelts right`;

val wmpnadd_rebased_snapshot_def = Define `
  wmpnadd_rebased_snapshot
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (fresh : 'p)
      (shared : 'p)
      (old : 'p) <=>
    wmpnadd_same_data data_length pelts fresh shared /\
    data_length shared = data_length old /\
    offset fresh = offset old /\
    minimum fresh = minimum old /\
    maximum fresh = maximum old /\
    writable fresh = writable old /\
    zone fresh = zone old`;

val wmpnadd_snapshot_metadata_def = Define `
  wmpnadd_snapshot_metadata
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (fresh : 'p)
      (old : 'p) <=>
    data_length fresh = data_length old /\
    offset fresh = offset old /\
    minimum fresh = minimum old /\
    maximum fresh = maximum old /\
    writable fresh = writable old /\
    zone fresh = zone old`;

val wmpnadd_disjoint_def = Define `
  wmpnadd_disjoint
      (offset : 'p -> int)
      (left : 'p)
      (left_size : int)
      (right : 'p)
      (right_size : int) <=>
    offset left = offset right \/
    offset left + left_size <= offset right \/
    offset right + right_size <= offset left`;

val wmpnadd_map_eq_sub_def = Define `
  wmpnadd_map_eq_sub
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      pelts left i = pelts right i`;

val wmpnadd_frame_def = Define `
  wmpnadd_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val wmpnadd_single_update_def = Define `
  wmpnadd_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val wmpnadd_access_def = Define `
  wmpnadd_access
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (index : int) <=>
    minimum p <= index /\ index < maximum p`;

val wmpnadd_carry_range_def = Define `
  wmpnadd_carry_range (carry : word64) <=>
    (0 : int) <= &(w2n carry) /\
    &(w2n carry) <= (1 : int)`;

val wmpnadd_zero_flag_def = Define `
  wmpnadd_zero_flag (limb : word64) (flag : bool) <=>
    ((&(w2n limb) = &(w2n (0w : word64))) ==> flag = T) /\
    (flag = T ==> limb = (0w : word64))`;

val wmpnadd_value_equation_def = Define `
  wmpnadd_value_equation
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (current : 'p)
      (x : 'p)
      (y : 'p)
      (index : int)
      (carry : word64) <=>
    wmpnadd_value pelts offset current index +
        wmpnadd_radix_power index * &(w2n carry) =
      wmpnadd_value pelts offset x index +
        wmpnadd_value pelts offset y (w2i sy)`;

val wmpnadd_alias_invariant_def = Define `
  wmpnadd_alias_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p)
      (x : 'p)
      (y : 'p) <=>
    pelts x_current = pelts current /\
    pelts y_current = pelts current /\
    (offset current = offset x_current \/
     wmpnadd_map_eq_sub
       pelts x_current x (offset x_current)
       (offset x_current + w2i sx)) /\
    (offset current = offset y_current \/
     wmpnadd_map_eq_sub
       pelts y_current y (offset y_current)
       (offset y_current + w2i sy))`;

val wmpnadd_initial_postcondition_def = Define `
  wmpnadd_initial_postcondition
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p)
      (carry : word64) <=>
    wmpnadd_value_equation
      offset pelts sy current x y (w2i sy) carry /\
    wmpnadd_carry_range carry /\
    wmpnadd_frame offset pelts current r (w2i sy) /\
    (offset current = offset x_current \/
     wmpnadd_map_eq_sub
       pelts x_current x (offset x_current)
       (offset x_current + w2i sy)) /\
    (offset current = offset y_current \/
     wmpnadd_map_eq_sub
       pelts y_current y (offset y_current)
       (offset y_current + w2i sy))`;

val wmpnadd_final_state_def = Define `
  wmpnadd_final_state
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p)
      (carry : word64) <=>
    wmpnadd_value_equation
      offset pelts sy current x y (w2i sx) carry /\
    wmpnadd_carry_range carry /\
    wmpnadd_frame offset pelts current r (w2i sx) /\
    (offset current = offset x_current \/
     wmpnadd_map_eq_sub
       pelts x_current x (offset x_current)
       (offset x_current + w2i sx)) /\
    (offset current = offset y_current \/
     wmpnadd_map_eq_sub
       pelts y_current y (offset y_current)
       (offset y_current + w2i sy))`;

val wmpnadd_carry_invariant_def = Define `
  wmpnadd_carry_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (carry : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    w2i sy <= w2i index /\ w2i index <= w2i sx /\
    wmpnadd_value_equation
      offset pelts sy current x y (w2i index) carry /\
    wmpnadd_frame offset pelts current r (w2i index) /\
    wmpnadd_alias_invariant
      offset pelts sy sx current x_current y_current x y /\
    wmpnadd_carry_range carry /\
    (index = sx \/ &(w2n carry) = (1 : int))`;

val wmpnadd_copy_invariant_def = Define `
  wmpnadd_copy_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (carry : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    w2i sy <= w2i index /\ w2i index <= w2i sx /\
    (index = sx \/ &(w2n carry) = (0 : int)) /\
    wmpnadd_value_equation
      offset pelts sy current x y (w2i index) carry /\
    wmpnadd_frame offset pelts current r (w2i index) /\
    wmpnadd_alias_invariant
      offset pelts sy sx current x_current y_current x y /\
    wmpnadd_carry_range carry`;

val wmpnadd_copy_step_def = Define `
  wmpnadd_copy_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (carry : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    if w2i index < w2i sx then
      wmpnadd_access
        minimum maximum x_current (offset x_current + w2i index) /\
      wmpnadd_access minimum maximum x (offset x + w2i index) /\
      (wmpnadd_access
         minimum maximum current (offset current + w2i index) /\
       writable current = T) /\
      (!y_next x_next r_next : 'p.
         wmpnadd_rebased_snapshot
           data_length pelts offset minimum maximum writable zone
           y_next r_next y_current ==>
         wmpnadd_rebased_snapshot
           data_length pelts offset minimum maximum writable zone
           x_next r_next x_current ==>
         wmpnadd_snapshot_metadata
           data_length offset minimum maximum writable zone
           r_next current ==>
         (wmpnadd_single_update
            pelts r_next current (offset r_next + w2i index)
            (pelts x_current (offset x_current + w2i index)) /\
          pelts r_next (offset r_next + w2i index) =
            pelts x_current (offset x_current + w2i index)) ==>
         wmpnadd_int32_in_bounds (w2i index + (1 : int)) /\
         (!next : word32.
            w2i next = w2i index + (1 : int) ==>
            ((0 : int) <= w2i sx - w2i index /\
             w2i sx - w2i next < w2i sx - w2i index) /\
            wmpnadd_copy_invariant
              offset pelts sy sx r x y next carry
              r_next x_next y_next))
    else
      wmpnadd_final_state
        offset pelts sy sx r x y current x_current y_current carry`;

val wmpnadd_copy_loop_def = Define `
  wmpnadd_copy_loop
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (carry : word64)
      (initial : 'p)
      (x_initial : 'p)
      (y_initial : 'p) <=>
    !index : word32.
    !y_current x_current current : 'p.
      wmpnadd_rebased_snapshot
        data_length pelts offset minimum maximum writable zone
        y_current current y_initial ==>
      wmpnadd_rebased_snapshot
        data_length pelts offset minimum maximum writable zone
        x_current current x_initial ==>
      wmpnadd_snapshot_metadata
        data_length offset minimum maximum writable zone current initial ==>
      wmpnadd_copy_invariant
        offset pelts sy sx r x y index carry
        current x_current y_current ==>
      wmpnadd_copy_step
        data_length offset minimum maximum writable zone pelts
        sy sx r x y index carry current x_current y_current`;

val wmpnadd_copy_phase_def = Define `
  wmpnadd_copy_phase
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (carry : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    wmpnadd_copy_invariant
      offset pelts sy sx r x y index carry current x_current y_current /\
    wmpnadd_copy_loop
      data_length offset minimum maximum writable zone pelts
      sy sx r x y carry current x_current y_current`;

val wmpnadd_carry_step_def = Define `
  wmpnadd_carry_step
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (carry : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    if w2i index < w2i sx then
      wmpnadd_access
        minimum maximum x_current (offset x_current + w2i index) /\
      wmpnadd_access minimum maximum x (offset x + w2i index) /\
      (!result : word64.
         &(w2n result) =
           (&(w2n (pelts x_current (offset x_current + w2i index))) +
            (1 : int)) rem wmpnadd_radix ==>
         (wmpnadd_access
            minimum maximum current (offset current + w2i index) /\
          writable current = T) /\
         (!y_next x_next r_next : 'p.
            wmpnadd_rebased_snapshot
              data_length pelts offset minimum maximum writable zone
              y_next r_next y_current ==>
            wmpnadd_rebased_snapshot
              data_length pelts offset minimum maximum writable zone
              x_next r_next x_current ==>
            wmpnadd_snapshot_metadata
              data_length offset minimum maximum writable zone
              r_next current ==>
            (wmpnadd_single_update
               pelts r_next current (offset r_next + w2i index) result /\
             pelts r_next (offset r_next + w2i index) = result) ==>
            wmpnadd_int32_in_bounds (w2i index + (1 : int)) /\
            (!next : word32.
               w2i next = w2i index + (1 : int) ==>
               (!flag : bool.
                  wmpnadd_zero_flag result flag ==>
                  if ~(flag = T) then
                    wmpnadd_copy_phase
                      data_length offset minimum maximum writable zone pelts
                      sy sx r x y next (0w : word64)
                      r_next x_next y_next
                  else
                    ((0 : int) <= w2i sx - w2i index /\
                     w2i sx - w2i next < w2i sx - w2i index) /\
                    wmpnadd_carry_invariant
                      offset pelts sy sx r x y next carry
                      r_next x_next y_next))))
    else
      wmpnadd_final_state
        offset pelts sy sx r x y current x_current y_current carry`;

val wmpnadd_carry_loop_def = Define `
  wmpnadd_carry_loop
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (initial : 'p)
      (x_initial : 'p)
      (y_initial : 'p) <=>
    !index : word32.
    !carry : word64.
    !y_current x_current current : 'p.
      wmpnadd_rebased_snapshot
        data_length pelts offset minimum maximum writable zone
        y_current current y_initial ==>
      wmpnadd_rebased_snapshot
        data_length pelts offset minimum maximum writable zone
        x_current current x_initial ==>
      wmpnadd_snapshot_metadata
        data_length offset minimum maximum writable zone current initial ==>
      wmpnadd_carry_invariant
        offset pelts sy sx r x y index carry
        current x_current y_current ==>
      wmpnadd_carry_step
        data_length offset minimum maximum writable zone pelts
        sy sx r x y index carry current x_current y_current`;

val wmpnadd_carry_phase_def = Define `
  wmpnadd_carry_phase
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (carry : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    wmpnadd_carry_invariant
      offset pelts sy sx r x y sy carry current x_current y_current /\
    wmpnadd_carry_loop
      data_length offset minimum maximum writable zone pelts
      sy sx r x y current x_current y_current`;

val wmpnadd_after_initial_flag_def = Define `
  wmpnadd_after_initial_flag
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (carry : word64)
      (flag : bool)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    if ~(flag = T) then
      wmpnadd_carry_phase
        data_length offset minimum maximum writable zone pelts
        sy sx r x y carry current x_current y_current
    else
      wmpnadd_copy_phase
        data_length offset minimum maximum writable zone pelts
        sy sx r x y sy carry current x_current y_current`;

val wmpnadd_after_initial_def = Define `
  wmpnadd_after_initial
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (carry : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    !flag : bool.
      wmpnadd_zero_flag carry flag ==>
      wmpnadd_after_initial_flag
        data_length offset minimum maximum writable zone pelts
        sy sx r x y carry flag current x_current y_current`;

val add_Add_wmpn_add_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !sy sx : word32.
    !r x y : 'p.
      (0 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      wmpnadd_valid
        data_length offset minimum maximum r (w2i sx) ==>
      wmpnadd_valid
        data_length offset minimum maximum x (w2i sx) ==>
      wmpnadd_valid
        data_length offset minimum maximum y (w2i sy) ==>
      wmpnadd_disjoint offset r (w2i sx) x (w2i sx) ==>
      wmpnadd_disjoint offset r (w2i sx) y (w2i sy) ==>
      wmpnadd_same_data data_length pelts r x ==>
      wmpnadd_same_data data_length pelts x y ==>
      writable r = T ==>
      (0 : int) <= w2i sy /\
      wmpnadd_valid
        data_length offset minimum maximum r (w2i sy) /\
      wmpnadd_valid
        data_length offset minimum maximum x (w2i sy) /\
      wmpnadd_valid
        data_length offset minimum maximum y (w2i sy) /\
      wmpnadd_disjoint offset r (w2i sy) x (w2i sy) /\
      wmpnadd_disjoint offset r (w2i sy) y (w2i sy) /\
      wmpnadd_same_data data_length pelts r x /\
      wmpnadd_same_data data_length pelts x y /\
      writable r = T /\
      (!y_current x_current current : 'p.
         wmpnadd_rebased_snapshot
           data_length pelts offset minimum maximum writable zone
           y_current current y ==>
         wmpnadd_rebased_snapshot
           data_length pelts offset minimum maximum writable zone
           x_current current x ==>
         wmpnadd_snapshot_metadata
           data_length offset minimum maximum writable zone current r ==>
         (!carry : word64.
            wmpnadd_initial_postcondition
              offset pelts sy r x y current x_current y_current carry ==>
            wmpnadd_after_initial
              data_length offset minimum maximum writable zone pelts
              sy sx r x y carry current x_current y_current))``;
