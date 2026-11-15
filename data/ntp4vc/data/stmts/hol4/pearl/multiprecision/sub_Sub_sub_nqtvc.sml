(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_sub_nqtvc: the verification condition for
  equal-length multiprecision subtraction into a separate result pointer,
  including borrow arithmetic, pointer aliasing, memory framing, and metadata
  preservation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val subn_radix_def = Define `
  subn_radix = (18446744073709551616 : int)`;

val subn_to_num_def = Define `
  subn_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val subn_int32_in_bounds_def = Define `
  subn_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val subn_plength_def = Define `
  subn_plength (data_length : 'p -> num) (p : 'p) =
    &(data_length p)`;

val subn_valid_def = Define `
  subn_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (size : int) <=>
    subn_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + size <= maximum p /\
    maximum p <= subn_plength data_length p`;

val subn_radix_power_def = Define `
  subn_radix_power (exponent : int) =
    subn_radix ** subn_to_num exponent`;

val subn_value_from_def = Define `
  (subn_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (subn_value_from pelts p index (SUC count) =
     &(w2n (pelts p index)) +
       subn_radix *
         subn_value_from pelts p (index + (1 : int)) count)`;

val subn_value_def = Define `
  subn_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (size : int) =
    subn_value_from
      pelts p (offset p) (subn_to_num size)`;

val subn_map_eq_sub_def = Define `
  subn_map_eq_sub
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      pelts left i = pelts right i`;

val subn_map_eq_sub_shift_def = Define `
  subn_map_eq_sub_shift
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p)
      (left_offset : int)
      (right_offset : int)
      (size : int) <=>
    !i : int.
      (0 : int) <= i /\ i < size ==>
      pelts left (left_offset + i) =
        pelts right (right_offset + i)`;

val subn_same_pelts_def = Define `
  subn_same_pelts
      (pelts : 'p -> int -> word64) (left : 'p) (right : 'p) <=>
    !i : int.
      pelts left i = pelts right i`;

val subn_same_data_def = Define `
  subn_same_data
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    subn_same_pelts pelts left right`;

val subn_view_eq_def = Define `
  subn_view_eq
      (offset : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (current : 'p)
      (original : 'p) <=>
    offset current = offset original /\
    writable current = writable original /\
    zone current = zone original`;

val subn_view_min_eq_def = Define `
  subn_view_min_eq
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (current : 'p)
      (original : 'p) <=>
    offset current = offset original /\
    minimum current = minimum original /\
    writable current = writable original /\
    zone current = zone original`;

val subn_nonoverlap_def = Define `
  subn_nonoverlap
      (offset : 'p -> int)
      (left : 'p)
      (right : 'p)
      (size : int) <=>
    offset left = offset right \/
    offset left + size <= offset right \/
    offset right + size <= offset left`;

val subn_ordered_three_def = Define `
  subn_ordered_three
      (offset : 'p -> int)
      (result : 'p)
      (first : 'p)
      (second : 'p)
      (size : int) <=>
    (0 : int) <= offset result /\
    offset result + size <= offset first /\
    offset first + size <= offset second`;

val subn_outside_unchanged_def = Define `
  subn_outside_unchanged
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (current : 'p)
      (original : 'p)
      (size : int) <=>
    !j : int.
      j < offset current \/ offset current + size <= j ==>
      pelts current j = pelts original j`;

val subn_same_alias_fields_def = Define `
  subn_same_alias_fields
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mr : 'm -> word32)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (current : 'm)
      (original : 'm) <=>
    zr current = zr original /\
    zx current = zx original /\
    zy current = zy original /\
    mr current = mr original /\
    mx current = mx original /\
    my current = my original /\
    lr current = lr original /\
    lx current = lx original /\
    ly current = ly original`;

val subn_ny_snapshot_def = Define `
  subn_ny_snapshot
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (ny1 : 'p)
      (nr1 : 'p)
      (ny : 'p) <=>
    subn_same_data data_length pelts ny1 nr1 /\
    data_length nr1 = data_length ny /\
    offset ny1 = offset ny /\
    minimum ny1 = minimum ny /\
    maximum ny1 = maximum ny /\
    writable ny1 = writable ny /\
    zone ny1 = zone ny`;

val subn_nx_snapshot_def = Define `
  subn_nx_snapshot
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (nx1 : 'p)
      (nr1 : 'p)
      (nx : 'p) <=>
    subn_same_data data_length pelts nx1 nr1 /\
    data_length nr1 = data_length nx /\
    offset nx1 = offset nx /\
    minimum nx1 = minimum nx /\
    maximum nx1 = maximum nx /\
    writable nx1 = writable nx /\
    zone nx1 = zone nx`;

val subn_nr_snapshot_def = Define `
  subn_nr_snapshot
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (nr1 : 'p)
      (nr : 'p) <=>
    data_length nr1 = data_length nr /\
    offset nr1 = offset nr /\
    minimum nr1 = minimum nr /\
    maximum nr1 = maximum nr /\
    writable nr1 = writable nr /\
    zone nr1 = zone nr`;

val subn_wmpn_postcondition_def = Define `
  subn_wmpn_postcondition
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (size : word32)
      (nr : 'p)
      (nx : 'p)
      (ny : 'p)
      (nr1 : 'p)
      (nx1 : 'p)
      (ny1 : 'p)
      (result : word64) <=>
    subn_value pelts offset nr1 (w2i size) -
        subn_radix_power (w2i size) * &(w2n result) =
      subn_value pelts offset nx (w2i size) -
        subn_value pelts offset ny (w2i size) /\
    ((0 : int) <= &(w2n result) /\ &(w2n result) <= (1 : int)) /\
    subn_outside_unchanged pelts offset nr1 nr (w2i size) /\
    (offset nr1 = offset nx1 \/
     subn_map_eq_sub
       pelts nx1 nx (offset nx1) (offset nx1 + w2i size)) /\
    (offset nr1 = offset ny1 \/
     subn_map_eq_sub
       pelts ny1 ny (offset ny1) (offset ny1 + w2i size))`;

val subn_close_precondition_def = Define `
  subn_close_precondition
      (offset : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (r1 : 'p)
      (x1 : 'p)
      (y1 : 'p)
      (nr1 : 'p)
      (nx1 : 'p)
      (ny1 : 'p)
      (m : 'm) <=>
    ok m = T /\
    ((0 : int) <= w2i size /\ w2i size <= w2i size) /\
    (zr m = zone r1 /\ zx m = zone x1 /\ zy m = zone y1) /\
    (lr m = size /\ lx m = size /\ ly m = size) /\
    subn_ordered_three offset nr1 nx1 ny1 (w2i size) /\
    writable r1 = T /\
    writable nr1 = T`;

val subn_final_postcondition_def = Define `
  subn_final_postcondition
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (size : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (r2 : 'p)
      (x2 : 'p)
      (y2 : 'p)
      (result : word64) <=>
    subn_value pelts offset r2 (w2i size) -
        subn_radix_power (w2i size) * &(w2n result) =
      subn_value pelts offset x (w2i size) -
        subn_value pelts offset y (w2i size) /\
    ((0 : int) <= &(w2n result) /\ &(w2n result) <= (1 : int)) /\
    subn_outside_unchanged pelts offset r2 r (w2i size) /\
    subn_same_pelts pelts x2 x /\
    subn_same_pelts pelts y2 y /\
    subn_value pelts offset x2 (w2i size) =
      subn_value pelts offset x (w2i size) /\
    subn_value pelts offset y2 (w2i size) =
      subn_value pelts offset y (w2i size) /\
    (minimum x2 = minimum x /\
     maximum x2 = maximum x /\
     subn_plength data_length x2 = subn_plength data_length x) /\
    (minimum y2 = minimum y /\
     maximum y2 = maximum y /\
     subn_plength data_length y2 = subn_plength data_length y) /\
    minimum r2 = minimum r /\
    maximum r2 = maximum r /\
    subn_plength data_length r2 = subn_plength data_length r`;

val subn_close_obligation_def = Define `
  subn_close_obligation
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mr : 'm -> word32)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (size : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (r1 : 'p)
      (x1 : 'p)
      (y1 : 'p)
      (nr1 : 'p)
      (nx1 : 'p)
      (ny1 : 'p)
      (m : 'm)
      (result : word64) <=>
    !m1 : 'm.
    !ny2 nx2 nr2 y2 x2 r2 : 'p.
      subn_same_alias_fields
        zr zx zy mr mx my lr lx ly m1 m ==>
      subn_view_eq offset writable zone ny2 ny1 ==>
      subn_view_eq offset writable zone nx2 nx1 ==>
      subn_view_eq offset writable zone nr2 nr1 ==>
      subn_view_min_eq offset minimum writable zone y2 y1 ==>
      subn_view_min_eq offset minimum writable zone x2 x1 ==>
      subn_view_min_eq offset minimum writable zone r2 r1 ==>
      ((maximum r2 = w2i (mr m1) /\
        maximum x2 = w2i (mx m1) /\
        maximum y2 = w2i (my m1)) /\
       subn_map_eq_sub_shift
         pelts nr1 r2 (offset nr2) (offset r2) (w2i size) /\
       subn_map_eq_sub_shift
         pelts nx1 x2 (offset nx2) (offset x2) (w2i size) /\
       subn_map_eq_sub_shift
         pelts ny1 y2 (offset ny2) (offset y2) (w2i size) /\
       subn_outside_unchanged pelts offset r2 r1 (w2i size) /\
       subn_outside_unchanged pelts offset x2 x1 (w2i size) /\
       subn_outside_unchanged pelts offset y2 y1 (w2i size) /\
       (subn_plength data_length r2 = subn_plength data_length r1 /\
        subn_plength data_length x2 = subn_plength data_length x1 /\
        subn_plength data_length y2 = subn_plength data_length y1) /\
       minimum r2 = minimum r1 /\
       minimum x2 = minimum x1 /\
       minimum y2 = minimum y1 ==>
       subn_final_postcondition
         data_length pelts offset minimum maximum
         size r x y r2 x2 y2 result)`;

val subn_after_wmpn_sub_def = Define `
  subn_after_wmpn_sub
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mr : 'm -> word32)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (r1 : 'p)
      (x1 : 'p)
      (y1 : 'p)
      (nr : 'p)
      (nx : 'p)
      (ny : 'p)
      (m : 'm) <=>
    !ny1 nx1 nr1 : 'p.
      subn_ny_snapshot
        data_length pelts offset minimum maximum writable zone
        ny1 nr1 ny ==>
      subn_nx_snapshot
        data_length pelts offset minimum maximum writable zone
        nx1 nr1 nx ==>
      subn_nr_snapshot
        data_length offset minimum maximum writable zone nr1 nr ==>
      (!result : word64.
         subn_wmpn_postcondition
           pelts offset size nr nx ny nr1 nx1 ny1 result ==>
         subn_close_precondition
           offset writable zone zr zx zy lr lx ly ok
           size r1 x1 y1 nr1 nx1 ny1 m /\
         subn_close_obligation
           data_length pelts offset minimum maximum writable zone
           zr zx zy mr mx my lr lx ly size
           r x y r1 x1 y1 nr1 nx1 ny1 m result)`;

val subn_opened_state_conclusion_def = Define `
  subn_opened_state_conclusion
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mr : 'm -> word32)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (r1 : 'p)
      (x1 : 'p)
      (y1 : 'p)
      (nr : 'p)
      (nx : 'p)
      (ny : 'p)
      (m : 'm) <=>
    ((0 : int) <= w2i size /\
     (subn_valid data_length offset minimum maximum nr (w2i size) /\
      subn_valid data_length offset minimum maximum nx (w2i size) /\
      subn_valid data_length offset minimum maximum ny (w2i size)) /\
     subn_nonoverlap offset nr nx (w2i size) /\
     subn_nonoverlap offset nr ny (w2i size) /\
     (subn_same_data data_length pelts nr nx /\
      subn_same_data data_length pelts nx ny) /\
     writable nr = T) /\
    subn_after_wmpn_sub
      data_length pelts offset minimum maximum writable zone
      zr zx zy mr mx my lr lx ly ok size
      r x y r1 x1 y1 nr nx ny m`;

val subn_open_sep_antecedent_def = Define `
  subn_open_sep_antecedent
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mr : 'm -> word32)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (r1 : 'p)
      (x1 : 'p)
      (y1 : 'p)
      (nr : 'p)
      (nx : 'p)
      (ny : 'p)
      (m : 'm) <=>
    writable nr = T /\
    (subn_value pelts offset nx (w2i size) =
       subn_value pelts offset x (w2i size) /\
     subn_value pelts offset ny (w2i size) =
       subn_value pelts offset y (w2i size)) /\
    (subn_valid data_length offset minimum maximum nr (w2i size) /\
     subn_valid data_length offset minimum maximum nx (w2i size) /\
     subn_valid data_length offset minimum maximum ny (w2i size)) /\
    subn_ordered_three offset nr nx ny (w2i size) /\
    (zr m = zone r1 /\ zx m = zone x1 /\ zy m = zone y1) /\
    (w2i (mr m) = maximum r /\
     w2i (mx m) = maximum x /\
     w2i (my m) = maximum y) /\
    (lr m = size /\ lx m = size /\ ly m = size) /\
    ok m = T /\
    subn_map_eq_sub_shift
      pelts nr r1 (offset nr) (offset r1) (w2i size) /\
    subn_map_eq_sub_shift
      pelts nx x1 (offset nx) (offset x1) (w2i size) /\
    subn_map_eq_sub_shift
      pelts ny y1 (offset ny) (offset y1) (w2i size) /\
    (subn_same_pelts pelts r1 r /\
     subn_same_pelts pelts x1 x /\
     subn_same_pelts pelts y1 y) /\
    (subn_plength data_length r1 = subn_plength data_length r /\
     subn_plength data_length x1 = subn_plength data_length x /\
     subn_plength data_length y1 = subn_plength data_length y) /\
    (minimum r1 = minimum r /\
     minimum x1 = minimum x /\
     minimum y1 = minimum y) /\
    subn_same_data data_length pelts nr nx /\
    subn_same_data data_length pelts nx ny`;

val subn_all_opened_states_def = Define `
  subn_all_opened_states
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mr : 'm -> word32)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p)
      (r1 : 'p)
      (x1 : 'p)
      (y1 : 'p) <=>
    !nr nx ny : 'p.
    !m : 'm.
      subn_open_sep_antecedent
        data_length pelts offset minimum maximum writable zone
        zr zx zy mr mx my lr lx ly ok size
        r x y r1 x1 y1 nr nx ny m ==>
      subn_opened_state_conclusion
        data_length pelts offset minimum maximum writable zone
        zr zx zy mr mx my lr lx ly ok size
        r x y r1 x1 y1 nr nx ny m`;

val subn_all_views_def = Define `
  subn_all_views
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mr : 'm -> word32)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (r : 'p)
      (x : 'p)
      (y : 'p) <=>
    !y1 x1 r1 : 'p.
      subn_view_eq offset writable zone y1 y ==>
      subn_view_eq offset writable zone x1 x ==>
      subn_view_eq offset writable zone r1 r ==>
      subn_all_opened_states
        data_length pelts offset minimum maximum writable zone
        zr zx zy mr mx my lr lx ly ok size
        r x y r1 x1 y1`;

val sub_Sub_sub_n_vc =
  ``!data_length : 'p -> num.
    !pelts : 'p -> int -> word64.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !zr zx zy : 'm -> 'z.
    !mr mx my lr lx ly : 'm -> word32.
    !ok : 'm -> bool.
    !size : word32.
    !r x y : 'p.
      (0 : int) <= w2i size ==>
      subn_valid data_length offset minimum maximum r (w2i size) ==>
      subn_valid data_length offset minimum maximum x (w2i size) ==>
      subn_valid data_length offset minimum maximum y (w2i size) ==>
      writable r = T ==>
      subn_valid data_length offset minimum maximum r (w2i size) /\
      subn_valid data_length offset minimum maximum x (w2i size) /\
      subn_valid data_length offset minimum maximum y (w2i size) /\
      writable r = T /\
      (0 : int) <= w2i size /\
      w2i size <= w2i size /\
      subn_all_views
        data_length pelts offset minimum maximum writable zone
        zr zx zy mr mx my lr lx ly ok size r x y``;
