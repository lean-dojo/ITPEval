(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_subqtvc: the verification condition for
  alias-aware unequal-length multiprecision subtraction into a separate
  result pointer, including borrow arithmetic, memory framing, validity,
  and preservation of operand data and pointer metadata. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val sub_radix_def = Define `
  sub_radix = (18446744073709551616 : int)`;

val sub_to_num_def = Define `
  sub_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val sub_int32_in_bounds_def = Define `
  sub_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val sub_plength_def = Define `
  sub_plength (data_length : 'p -> num) (p : 'p) =
    &(data_length p)`;

val sub_valid_def = Define `
  sub_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (size : int) <=>
    sub_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + size <= maximum p /\
    maximum p <= sub_plength data_length p`;

val sub_radix_power_def = Define `
  sub_radix_power (exponent : int) =
    sub_radix ** sub_to_num exponent`;

val sub_value_from_def = Define `
  (sub_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (sub_value_from pelts p index (SUC count) =
     &(w2n (pelts p index)) +
       sub_radix *
         sub_value_from pelts p (index + (1 : int)) count)`;

val sub_value_def = Define `
  sub_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (size : int) =
    sub_value_from pelts p (offset p) (sub_to_num size)`;

val sub_map_eq_sub_shift_def = Define `
  sub_map_eq_sub_shift
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p)
      (left_start : int)
      (right_start : int)
      (size : int) <=>
    !i : int.
      (0 : int) <= i /\ i < size ==>
      pelts left (left_start + i) =
        pelts right (right_start + i)`;

val sub_map_eq_sub_def = Define `
  sub_map_eq_sub
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      pelts left i = pelts right i`;

val sub_outside_equal_def = Define `
  sub_outside_equal
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (newp : 'p)
      (oldp : 'p)
      (size : int) <=>
    !j : int.
      j < offset newp \/ offset newp + size <= j ==>
      pelts newp j = pelts oldp j`;

val sub_same_pelts_def = Define `
  sub_same_pelts
      (pelts : 'p -> int -> word64) (left : 'p) (right : 'p) <=>
    !j : int.
      pelts left j = pelts right j`;

val sub_same_data_def = Define `
  sub_same_data
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    sub_same_pelts pelts left right`;

val sub_view_def = Define `
  sub_view
      (offset : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (current : 'p)
      (oldp : 'p) <=>
    offset current = offset oldp /\
    writable current = writable oldp /\
    zone current = zone oldp`;

val sub_view_with_minimum_def = Define `
  sub_view_with_minimum
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (current : 'p)
      (oldp : 'p) <=>
    offset current = offset oldp /\
    minimum current = minimum oldp /\
    writable current = writable oldp /\
    zone current = zone oldp`;

val sub_memory_view_def = Define `
  sub_memory_view
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
      (oldm : 'm) <=>
    zr current = zr oldm /\
    zx current = zx oldm /\
    zy current = zy oldm /\
    mr current = mr oldm /\
    mx current = mx oldm /\
    my current = my oldm /\
    lr current = lr oldm /\
    lx current = lx oldm /\
    ly current = ly oldm`;

val sub_Sub_sub_vc =
  ``!data_length : 'p -> num.
    !pelts : 'p -> int -> word64.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !zr zx zy : 'm -> 'z.
    !mr mx my lr lx ly : 'm -> word32.
    !ok : 'm -> bool.
    !sy sx : word32.
    !r x y : 'p.
      (0 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      sub_valid data_length offset minimum maximum r (w2i sx) ==>
      sub_valid data_length offset minimum maximum x (w2i sx) ==>
      sub_valid data_length offset minimum maximum y (w2i sy) ==>
      writable r = T ==>
      sub_valid data_length offset minimum maximum r (w2i sx) /\
      sub_valid data_length offset minimum maximum x (w2i sx) /\
      sub_valid data_length offset minimum maximum y (w2i sy) /\
      writable r = T /\
      (0 : int) <= w2i sy /\
      w2i sy <= w2i sx /\
      (!y1 x1 r1 : 'p.
         sub_view offset writable zone y1 y ==>
         sub_view offset writable zone x1 x ==>
         sub_view offset writable zone r1 r ==>
         (!nr nx ny : 'p.
          !m : 'm.
            writable nr = T /\
            (sub_value pelts offset nx (w2i sx) =
               sub_value pelts offset x (w2i sx) /\
             sub_value pelts offset ny (w2i sy) =
               sub_value pelts offset y (w2i sy)) /\
            (sub_valid data_length offset minimum maximum nr (w2i sx) /\
             sub_valid data_length offset minimum maximum nx (w2i sx) /\
             sub_valid data_length offset minimum maximum ny (w2i sy)) /\
            ((0 : int) <= offset nr /\
             offset nr + w2i sx <= offset nx /\
             offset nx + w2i sx <= offset ny) /\
            (zr m = zone r1 /\ zx m = zone x1 /\ zy m = zone y1) /\
            (w2i (mr m) = maximum r /\
             w2i (mx m) = maximum x /\
             w2i (my m) = maximum y) /\
            (lr m = sx /\ lx m = sx /\ ly m = sy) /\
            ok m = T /\
            sub_map_eq_sub_shift
              pelts nr r1 (offset nr) (offset r1) (w2i sx) /\
            sub_map_eq_sub_shift
              pelts nx x1 (offset nx) (offset x1) (w2i sx) /\
            sub_map_eq_sub_shift
              pelts ny y1 (offset ny) (offset y1) (w2i sy) /\
            (sub_same_pelts pelts r1 r /\
             sub_same_pelts pelts x1 x /\
             sub_same_pelts pelts y1 y) /\
            (sub_plength data_length r1 = sub_plength data_length r /\
             sub_plength data_length x1 = sub_plength data_length x /\
             sub_plength data_length y1 = sub_plength data_length y) /\
            (minimum r1 = minimum r /\
             minimum x1 = minimum x /\
             minimum y1 = minimum y) /\
            sub_same_data data_length pelts nr nx /\
            sub_same_data data_length pelts nx ny ==>
            (((0 : int) <= w2i sy /\ w2i sy <= w2i sx) /\
             (sub_valid data_length offset minimum maximum nr (w2i sx) /\
              sub_valid data_length offset minimum maximum nx (w2i sx) /\
              sub_valid data_length offset minimum maximum ny (w2i sy)) /\
             (offset nr = offset nx \/
              offset nr + w2i sx <= offset nx \/
              offset nx + w2i sx <= offset nr) /\
             (offset nr = offset ny \/
              offset nr + w2i sx <= offset ny \/
              offset ny + w2i sy <= offset nr) /\
             (sub_same_data data_length pelts nr nx /\
              sub_same_data data_length pelts nx ny) /\
             writable nr = T) /\
            (!ny1 nx1 nr1 : 'p.
               sub_same_data data_length pelts ny1 nr1 /\
               data_length nr1 = data_length ny /\
               offset ny1 = offset ny /\
               minimum ny1 = minimum ny /\
               maximum ny1 = maximum ny /\
               writable ny1 = writable ny /\
               zone ny1 = zone ny ==>
               sub_same_data data_length pelts nx1 nr1 /\
               data_length nr1 = data_length nx /\
               offset nx1 = offset nx /\
               minimum nx1 = minimum nx /\
               maximum nx1 = maximum nx /\
               writable nx1 = writable nx /\
               zone nx1 = zone nx ==>
               data_length nr1 = data_length nr /\
               offset nr1 = offset nr /\
               minimum nr1 = minimum nr /\
               maximum nr1 = maximum nr /\
               writable nr1 = writable nr /\
               zone nr1 = zone nr ==>
               (!result : word64.
                  sub_value pelts offset nr1 (w2i sx) -
                      sub_radix_power (w2i sx) * &(w2n result) =
                    sub_value pelts offset nx (w2i sx) -
                      sub_value pelts offset ny (w2i sy) /\
                  ((0 : int) <= &(w2n result) /\
                   &(w2n result) <= (1 : int)) /\
                  sub_outside_equal pelts offset nr1 nr (w2i sx) /\
                  (offset nr1 = offset nx1 \/
                   sub_map_eq_sub
                     pelts nx1 nx
                     (offset nx1) (offset nx1 + w2i sx)) /\
                  (offset nr1 = offset ny1 \/
                   sub_map_eq_sub
                     pelts ny1 ny
                     (offset ny1) (offset ny1 + w2i sy)) ==>
                  (ok m = T /\
                   ((0 : int) <= w2i sy /\ w2i sy <= w2i sx) /\
                   (zr m = zone r1 /\
                    zx m = zone x1 /\
                    zy m = zone y1) /\
                   (lr m = sx /\ lx m = sx /\ ly m = sy) /\
                   ((0 : int) <= offset nr1 /\
                    offset nr1 + w2i sx <= offset nx1 /\
                    offset nx1 + w2i sx <= offset ny1) /\
                   writable r1 = T /\
                   writable nr1 = T) /\
                  (!m1 : 'm.
                   !ny2 nx2 nr2 y2 x2 r2 : 'p.
                     sub_memory_view
                       zr zx zy mr mx my lr lx ly m1 m ==>
                     sub_view offset writable zone ny2 ny1 ==>
                     sub_view offset writable zone nx2 nx1 ==>
                     sub_view offset writable zone nr2 nr1 ==>
                     sub_view_with_minimum
                       offset minimum writable zone y2 y1 ==>
                     sub_view_with_minimum
                       offset minimum writable zone x2 x1 ==>
                     sub_view_with_minimum
                       offset minimum writable zone r2 r1 ==>
                     (maximum r2 = w2i (mr m1) /\
                      maximum x2 = w2i (mx m1) /\
                      maximum y2 = w2i (my m1)) /\
                     sub_map_eq_sub_shift
                       pelts nr1 r2
                       (offset nr2) (offset r2) (w2i sx) /\
                     sub_map_eq_sub_shift
                       pelts nx1 x2
                       (offset nx2) (offset x2) (w2i sx) /\
                     sub_map_eq_sub_shift
                       pelts ny1 y2
                       (offset ny2) (offset y2) (w2i sy) /\
                     sub_outside_equal pelts offset r2 r1 (w2i sx) /\
                     sub_outside_equal pelts offset x2 x1 (w2i sx) /\
                     sub_outside_equal pelts offset y2 y1 (w2i sy) /\
                     (sub_plength data_length r2 =
                        sub_plength data_length r1 /\
                      sub_plength data_length x2 =
                        sub_plength data_length x1 /\
                      sub_plength data_length y2 =
                        sub_plength data_length y1) /\
                     minimum r2 = minimum r1 /\
                     minimum x2 = minimum x1 /\
                     minimum y2 = minimum y1 ==>
                     sub_value pelts offset r2 (w2i sx) -
                         sub_radix_power (w2i sx) * &(w2n result) =
                       sub_value pelts offset x (w2i sx) -
                         sub_value pelts offset y (w2i sy) /\
                     ((0 : int) <= &(w2n result) /\
                      &(w2n result) <= (1 : int)) /\
                     sub_outside_equal pelts offset r2 r (w2i sx) /\
                     sub_same_pelts pelts x2 x /\
                     sub_same_pelts pelts y2 y /\
                     sub_value pelts offset x2 (w2i sx) =
                       sub_value pelts offset x (w2i sx) /\
                     sub_value pelts offset y2 (w2i sy) =
                       sub_value pelts offset y (w2i sy) /\
                     (minimum x2 = minimum x /\
                      maximum x2 = maximum x /\
                      sub_plength data_length x2 =
                        sub_plength data_length x) /\
                     (minimum y2 = minimum y /\
                      maximum y2 = maximum y /\
                      sub_plength data_length y2 =
                        sub_plength data_length y) /\
                     minimum r2 = minimum r /\
                     maximum r2 = maximum r /\
                     sub_plength data_length r2 =
                       sub_plength data_length r))))``;
