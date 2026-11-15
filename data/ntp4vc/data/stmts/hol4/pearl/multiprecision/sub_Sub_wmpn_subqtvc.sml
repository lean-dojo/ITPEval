(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_wmpn_subqtvc: the verification condition for
  unequal-length multiprecision subtraction into a separate result pointer,
  including the equal-prefix subtraction result, borrow propagation, copying
  remaining limbs, pointer aliasing, map updates, and memory framing. This
  file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val wmpnsub_radix_def = Define `
  wmpnsub_radix = (18446744073709551616 : int)`;

val wmpnsub_to_num_def = Define `
  wmpnsub_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val wmpnsub_int32_in_bounds_def = Define `
  wmpnsub_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val wmpnsub_radix_power_def = Define `
  wmpnsub_radix_power (n : int) =
    wmpnsub_radix ** wmpnsub_to_num n`;

val wmpnsub_value_from_def = Define `
  (wmpnsub_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (wmpnsub_value_from pelts p index (SUC count) =
     &(w2n (pelts p index)) +
       wmpnsub_radix *
         wmpnsub_value_from pelts p (index + (1 : int)) count)`;

val wmpnsub_value_def = Define `
  wmpnsub_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (count : int) =
    wmpnsub_value_from pelts p (offset p) (wmpnsub_to_num count)`;

val wmpnsub_valid_def = Define `
  wmpnsub_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (count : int) <=>
    wmpnsub_int32_in_bounds count /\
    (0 : int) <= count /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + count <= maximum p /\
    maximum p <= &(data_length p)`;

val wmpnsub_same_data_def = Define `
  wmpnsub_same_data
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    pelts left = pelts right`;

val wmpnsub_rebased_snapshot_def = Define `
  wmpnsub_rebased_snapshot
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
    wmpnsub_same_data data_length pelts fresh shared /\
    data_length shared = data_length old /\
    offset fresh = offset old /\
    minimum fresh = minimum old /\
    maximum fresh = maximum old /\
    writable fresh = writable old /\
    zone fresh = zone old`;

val wmpnsub_snapshot_metadata_def = Define `
  wmpnsub_snapshot_metadata
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

val wmpnsub_disjoint_def = Define `
  wmpnsub_disjoint
      (offset : 'p -> int)
      (left : 'p)
      (left_size : int)
      (right : 'p)
      (right_size : int) <=>
    offset left = offset right \/
    offset left + left_size <= offset right \/
    offset right + right_size <= offset left`;

val wmpnsub_map_eq_sub_def = Define `
  wmpnsub_map_eq_sub
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      pelts left i = pelts right i`;

val wmpnsub_frame_def = Define `
  wmpnsub_frame
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (count : int) <=>
    !j : int.
      j < offset new \/ offset new + count <= j ==>
      pelts new j = pelts old j`;

val wmpnsub_single_update_def = Define `
  wmpnsub_single_update
      (pelts : 'p -> int -> word64)
      (new : 'p)
      (old : 'p)
      (index : int)
      (value : word64) <=>
    !j : int.
      pelts new j =
        if j = index then value else pelts old j`;

val wmpnsub_access_def = Define `
  wmpnsub_access
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (index : int) <=>
    minimum p <= index /\ index < maximum p`;

val wmpnsub_borrow_range_def = Define `
  wmpnsub_borrow_range (borrow : word64) <=>
    (0 : int) <= &(w2n borrow) /\
    &(w2n borrow) <= (1 : int)`;

val wmpnsub_zero_flag_def = Define `
  wmpnsub_zero_flag (limb : word64) (flag : bool) <=>
    ((&(w2n limb) = &(w2n (0w : word64))) ==> flag = T) /\
    (flag = T ==> limb = (0w : word64))`;

val wmpnsub_value_equation_def = Define `
  wmpnsub_value_equation
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (current : 'p)
      (x : 'p)
      (y : 'p)
      (index : int)
      (borrow : word64) <=>
    wmpnsub_value pelts offset current index -
        wmpnsub_radix_power index * &(w2n borrow) =
      wmpnsub_value pelts offset x index -
        wmpnsub_value pelts offset y (w2i sy)`;

val wmpnsub_alias_invariant_def = Define `
  wmpnsub_alias_invariant
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
     wmpnsub_map_eq_sub
       pelts x_current x (offset x_current)
       (offset x_current + w2i sx)) /\
    (offset current = offset y_current \/
     wmpnsub_map_eq_sub
       pelts y_current y (offset y_current)
       (offset y_current + w2i sy))`;

val wmpnsub_initial_postcondition_def = Define `
  wmpnsub_initial_postcondition
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p)
      (borrow : word64) <=>
    wmpnsub_value_equation
      offset pelts sy current x y (w2i sy) borrow /\
    wmpnsub_borrow_range borrow /\
    wmpnsub_frame offset pelts current r (w2i sy) /\
    (offset current = offset x_current \/
     wmpnsub_map_eq_sub
       pelts x_current x (offset x_current)
       (offset x_current + w2i sy)) /\
    (offset current = offset y_current \/
     wmpnsub_map_eq_sub
       pelts y_current y (offset y_current)
       (offset y_current + w2i sy))`;

val wmpnsub_final_state_def = Define `
  wmpnsub_final_state
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
      (borrow : word64) <=>
    wmpnsub_value_equation
      offset pelts sy current x y (w2i sx) borrow /\
    wmpnsub_borrow_range borrow /\
    wmpnsub_frame offset pelts current r (w2i sx) /\
    (offset current = offset x_current \/
     wmpnsub_map_eq_sub
       pelts x_current x (offset x_current)
       (offset x_current + w2i sx)) /\
    (offset current = offset y_current \/
     wmpnsub_map_eq_sub
       pelts y_current y (offset y_current)
       (offset y_current + w2i sy))`;

val wmpnsub_borrow_invariant_def = Define `
  wmpnsub_borrow_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    w2i sy <= w2i index /\ w2i index <= w2i sx /\
    wmpnsub_value_equation
      offset pelts sy current x y (w2i index) borrow /\
    wmpnsub_frame offset pelts current r (w2i index) /\
    wmpnsub_alias_invariant
      offset pelts sy sx current x_current y_current x y /\
    wmpnsub_borrow_range borrow /\
    (index = sx \/ &(w2n borrow) = (1 : int))`;

val wmpnsub_copy_invariant_def = Define `
  wmpnsub_copy_invariant
      (offset : 'p -> int)
      (pelts : 'p -> int -> word64)
      (sy : word32)
      (sx : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (index : word32)
      (borrow : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    w2i sy <= w2i index /\ w2i index <= w2i sx /\
    (index = sx \/ &(w2n borrow) = (0 : int)) /\
    wmpnsub_value_equation
      offset pelts sy current x y (w2i index) borrow /\
    wmpnsub_frame offset pelts current r (w2i index) /\
    wmpnsub_alias_invariant
      offset pelts sy sx current x_current y_current x y /\
    wmpnsub_borrow_range borrow`;

val wmpnsub_copy_step_def = Define `
  wmpnsub_copy_step
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
      (borrow : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    if w2i index < w2i sx then
      wmpnsub_access
        minimum maximum x_current (offset x_current + w2i index) /\
      wmpnsub_access minimum maximum x (offset x + w2i index) /\
      (wmpnsub_access
         minimum maximum current (offset current + w2i index) /\
       writable current = T) /\
      (!y_next x_next r_next : 'p.
         wmpnsub_rebased_snapshot
           data_length pelts offset minimum maximum writable zone
           y_next r_next y_current ==>
         wmpnsub_rebased_snapshot
           data_length pelts offset minimum maximum writable zone
           x_next r_next x_current ==>
         wmpnsub_snapshot_metadata
           data_length offset minimum maximum writable zone
           r_next current ==>
         (wmpnsub_single_update
            pelts r_next current (offset r_next + w2i index)
            (pelts x_current (offset x_current + w2i index)) /\
          pelts r_next (offset r_next + w2i index) =
            pelts x_current (offset x_current + w2i index)) ==>
         wmpnsub_int32_in_bounds (w2i index + (1 : int)) /\
         (!next : word32.
            w2i next = w2i index + (1 : int) ==>
            ((0 : int) <= w2i sx - w2i index /\
             w2i sx - w2i next < w2i sx - w2i index) /\
            wmpnsub_copy_invariant
              offset pelts sy sx r x y next borrow
              r_next x_next y_next))
    else
      wmpnsub_final_state
        offset pelts sy sx r x y current x_current y_current borrow`;

val wmpnsub_copy_loop_def = Define `
  wmpnsub_copy_loop
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
      (borrow : word64)
      (initial : 'p)
      (x_initial : 'p)
      (y_initial : 'p) <=>
    !index : word32.
    !y_current x_current current : 'p.
      wmpnsub_rebased_snapshot
        data_length pelts offset minimum maximum writable zone
        y_current current y_initial ==>
      wmpnsub_rebased_snapshot
        data_length pelts offset minimum maximum writable zone
        x_current current x_initial ==>
      wmpnsub_snapshot_metadata
        data_length offset minimum maximum writable zone current initial ==>
      wmpnsub_copy_invariant
        offset pelts sy sx r x y index borrow
        current x_current y_current ==>
      wmpnsub_copy_step
        data_length offset minimum maximum writable zone pelts
        sy sx r x y index borrow current x_current y_current`;

val wmpnsub_copy_phase_def = Define `
  wmpnsub_copy_phase
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
      (borrow : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    wmpnsub_copy_invariant
      offset pelts sy sx r x y index borrow current x_current y_current /\
    wmpnsub_copy_loop
      data_length offset minimum maximum writable zone pelts
      sy sx r x y borrow current x_current y_current`;

val wmpnsub_borrow_step_def = Define `
  wmpnsub_borrow_step
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
      (borrow : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    if w2i index < w2i sx then
      wmpnsub_access
        minimum maximum x_current (offset x_current + w2i index) /\
      wmpnsub_access minimum maximum x (offset x + w2i index) /\
      (!result : word64.
         &(w2n result) =
           (&(w2n (pelts x_current (offset x_current + w2i index))) -
            (1 : int)) % wmpnsub_radix ==>
         (wmpnsub_access
            minimum maximum current (offset current + w2i index) /\
          writable current = T) /\
         (!y_next x_next r_next : 'p.
            wmpnsub_rebased_snapshot
              data_length pelts offset minimum maximum writable zone
              y_next r_next y_current ==>
            wmpnsub_rebased_snapshot
              data_length pelts offset minimum maximum writable zone
              x_next r_next x_current ==>
            wmpnsub_snapshot_metadata
              data_length offset minimum maximum writable zone
              r_next current ==>
            (wmpnsub_single_update
               pelts r_next current (offset r_next + w2i index) result /\
             pelts r_next (offset r_next + w2i index) = result) ==>
            wmpnsub_int32_in_bounds (w2i index + (1 : int)) /\
            (!next : word32.
               w2i next = w2i index + (1 : int) ==>
               (!flag : bool.
                  wmpnsub_zero_flag
                    (pelts x_current (offset x_current + w2i index))
                    flag ==>
                  if ~(flag = T) then
                    wmpnsub_copy_phase
                      data_length offset minimum maximum writable zone pelts
                      sy sx r x y next (0w : word64)
                      r_next x_next y_next
                  else
                    ((0 : int) <= w2i sx - w2i index /\
                     w2i sx - w2i next < w2i sx - w2i index) /\
                    wmpnsub_borrow_invariant
                      offset pelts sy sx r x y next borrow
                      r_next x_next y_next))))
    else
      wmpnsub_copy_phase
        data_length offset minimum maximum writable zone pelts
        sy sx r x y index borrow current x_current y_current`;

val wmpnsub_borrow_loop_def = Define `
  wmpnsub_borrow_loop
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
    !borrow : word64.
    !y_current x_current current : 'p.
      wmpnsub_rebased_snapshot
        data_length pelts offset minimum maximum writable zone
        y_current current y_initial ==>
      wmpnsub_rebased_snapshot
        data_length pelts offset minimum maximum writable zone
        x_current current x_initial ==>
      wmpnsub_snapshot_metadata
        data_length offset minimum maximum writable zone current initial ==>
      wmpnsub_borrow_invariant
        offset pelts sy sx r x y index borrow
        current x_current y_current ==>
      wmpnsub_borrow_step
        data_length offset minimum maximum writable zone pelts
        sy sx r x y index borrow current x_current y_current`;

val wmpnsub_borrow_phase_def = Define `
  wmpnsub_borrow_phase
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
      (borrow : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    wmpnsub_borrow_invariant
      offset pelts sy sx r x y sy borrow current x_current y_current /\
    wmpnsub_borrow_loop
      data_length offset minimum maximum writable zone pelts
      sy sx r x y current x_current y_current`;

val wmpnsub_after_initial_flag_def = Define `
  wmpnsub_after_initial_flag
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
      (borrow : word64)
      (flag : bool)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    if ~(flag = T) then
      wmpnsub_borrow_phase
        data_length offset minimum maximum writable zone pelts
        sy sx r x y borrow current x_current y_current
    else
      wmpnsub_copy_phase
        data_length offset minimum maximum writable zone pelts
        sy sx r x y sy borrow current x_current y_current`;

val wmpnsub_after_initial_def = Define `
  wmpnsub_after_initial
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
      (borrow : word64)
      (current : 'p)
      (x_current : 'p)
      (y_current : 'p) <=>
    !flag : bool.
      wmpnsub_zero_flag borrow flag ==>
      wmpnsub_after_initial_flag
        data_length offset minimum maximum writable zone pelts
        sy sx r x y borrow flag current x_current y_current`;

val sub_Sub_wmpn_sub_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !sy sx : word32.
    !r x y : 'p.
      (0 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      wmpnsub_valid
        data_length offset minimum maximum r (w2i sx) ==>
      wmpnsub_valid
        data_length offset minimum maximum x (w2i sx) ==>
      wmpnsub_valid
        data_length offset minimum maximum y (w2i sy) ==>
      wmpnsub_disjoint offset r (w2i sx) x (w2i sx) ==>
      wmpnsub_disjoint offset r (w2i sx) y (w2i sy) ==>
      wmpnsub_same_data data_length pelts r x ==>
      wmpnsub_same_data data_length pelts x y ==>
      writable r = T ==>
      (0 : int) <= w2i sy /\
      wmpnsub_valid
        data_length offset minimum maximum r (w2i sy) /\
      wmpnsub_valid
        data_length offset minimum maximum x (w2i sy) /\
      wmpnsub_valid
        data_length offset minimum maximum y (w2i sy) /\
      wmpnsub_disjoint offset r (w2i sy) x (w2i sy) /\
      wmpnsub_disjoint offset r (w2i sy) y (w2i sy) /\
      wmpnsub_same_data data_length pelts r x /\
      wmpnsub_same_data data_length pelts x y /\
      writable r = T /\
      (!y_current x_current current : 'p.
         wmpnsub_rebased_snapshot
           data_length pelts offset minimum maximum writable zone
           y_current current y ==>
         wmpnsub_rebased_snapshot
           data_length pelts offset minimum maximum writable zone
           x_current current x ==>
         wmpnsub_snapshot_metadata
           data_length offset minimum maximum writable zone current r ==>
         (!borrow : word64.
            wmpnsub_initial_postcondition
              offset pelts sy r x y current x_current y_current borrow ==>
            wmpnsub_after_initial
              data_length offset minimum maximum writable zone pelts
              sy sx r x y borrow current x_current y_current))``;
