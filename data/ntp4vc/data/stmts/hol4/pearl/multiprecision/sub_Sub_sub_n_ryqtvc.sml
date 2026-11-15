(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_sub_n_ryqtvc: the verification condition for
  equal-length multiprecision subtraction into the second operand, including
  borrow arithmetic, pointer validity, alias separation, memory framing, and
  preservation of pointer metadata. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val subnry_radix_def = Define `
  subnry_radix = (18446744073709551616 : int)`;

val subnry_to_num_def = Define `
  subnry_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val subnry_int32_in_bounds_def = Define `
  subnry_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val subnry_pelts_def = Define `
  subnry_pelts
      (data : 'p -> word64 list) (p : 'p) (index : int) =
    if subnry_to_num index < LENGTH (data p) then
      EL (subnry_to_num index) (data p)
    else
      (0w : word64)`;

val subnry_plength_def = Define `
  subnry_plength (data : 'p -> word64 list) (p : 'p) =
    &(LENGTH (data p))`;

val subnry_valid_def = Define `
  subnry_valid
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (size : int) <=>
    subnry_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + size <= maximum p /\
    maximum p <= subnry_plength data p`;

val subnry_radix_power_def = Define `
  subnry_radix_power (exponent : int) =
    subnry_radix ** subnry_to_num exponent`;

val subnry_value_from_def = Define `
  (subnry_value_from
      (data : 'p -> word64 list) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (subnry_value_from data p index (SUC count) =
     &(w2n (subnry_pelts data p index)) +
       subnry_radix *
         subnry_value_from data p (index + (1 : int)) count)`;

val subnry_value_def = Define `
  subnry_value
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (p : 'p)
      (size : int) =
    subnry_value_from
      data p (offset p) (subnry_to_num size)`;

val subnry_map_eq_sub_def = Define `
  subnry_map_eq_sub
      (data : 'p -> word64 list)
      (left : 'p)
      (right : 'p)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      subnry_pelts data left i = subnry_pelts data right i`;

val subnry_map_eq_sub_shift_def = Define `
  subnry_map_eq_sub_shift
      (data : 'p -> word64 list)
      (left : 'p)
      (right : 'p)
      (left_offset : int)
      (right_offset : int)
      (size : int) <=>
    !i : int.
      (0 : int) <= i /\ i < size ==>
      subnry_pelts data left (left_offset + i) =
        subnry_pelts data right (right_offset + i)`;

val subnry_same_pelts_def = Define `
  subnry_same_pelts
      (data : 'p -> word64 list) (left : 'p) (right : 'p) <=>
    !i : int.
      subnry_pelts data left i = subnry_pelts data right i`;

val subnry_identical_def = Define `
  subnry_identical
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (zone : 'p -> 'z)
      (left : 'p)
      (right : 'p) <=>
    data left = data right /\
    offset left = offset right /\
    minimum left = minimum right /\
    maximum left = maximum right /\
    zone left = zone right`;

val subnry_same_offset_writable_zone_def = Define `
  subnry_same_offset_writable_zone
      (offset : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (left : 'p)
      (right : 'p) <=>
    offset left = offset right /\
    writable left = writable right /\
    zone left = zone right`;

val subnry_same_offset_minimum_writable_zone_def = Define `
  subnry_same_offset_minimum_writable_zone
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (left : 'p)
      (right : 'p) <=>
    offset left = offset right /\
    minimum left = minimum right /\
    writable left = writable right /\
    zone left = zone right`;

val subnry_disjoint_def = Define `
  subnry_disjoint
      (offset : 'p -> int)
      (left : 'p)
      (right : 'p)
      (size : int) <=>
    offset left = offset right \/
    offset left + size <= offset right \/
    offset right + size <= offset left`;

val subnry_nonoverlap_def = Define `
  subnry_nonoverlap
      (offset : 'p -> int)
      (left : 'p)
      (right : 'p)
      (size : int) <=>
    ((0 : int) <= offset left /\
     offset left + size <= offset right) \/
    ((0 : int) <= offset right /\
     offset right + size <= offset left)`;

val subnry_open_precondition_def = Define `
  subnry_open_precondition
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (x : 'p)
      (y : 'p)
      (y1 : 'p)
      (x1 : 'p)
      (nr : 'p)
      (ny : 'p)
      (nx : 'p)
      (m : 'm) <=>
    writable nr = T /\
    subnry_value data offset ny (w2i size) =
      subnry_value data offset y (w2i size) /\
    subnry_value data offset nx (w2i size) =
      subnry_value data offset x (w2i size) /\
    subnry_valid data offset minimum maximum ny (w2i size) /\
    subnry_valid data offset minimum maximum nx (w2i size) /\
    subnry_identical data offset minimum maximum zone nr ny /\
    subnry_nonoverlap offset ny nx (w2i size) /\
    zx m = zone y1 /\
    zy m = zone x1 /\
    w2i (mx m) = maximum y /\
    w2i (my m) = maximum x /\
    lx m = size /\
    ly m = size /\
    ok m = T /\
    subnry_map_eq_sub_shift
      data ny y1 (offset ny) (offset y1) (w2i size) /\
    subnry_map_eq_sub_shift
      data nx x1 (offset nx) (offset x1) (w2i size) /\
    subnry_same_pelts data y1 y /\
    subnry_same_pelts data x1 x /\
    subnry_plength data y1 = subnry_plength data y /\
    subnry_plength data x1 = subnry_plength data x /\
    minimum y1 = minimum y /\
    minimum x1 = minimum x /\
    data nr = data ny /\
    data ny = data nx`;

val subnry_call_precondition_def = Define `
  subnry_call_precondition
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (size : word32)
      (nr : 'p)
      (nx : 'p)
      (ny : 'p) <=>
    (0 : int) <= w2i size /\
    subnry_valid data offset minimum maximum nr (w2i size) /\
    subnry_valid data offset minimum maximum nx (w2i size) /\
    subnry_valid data offset minimum maximum ny (w2i size) /\
    subnry_disjoint offset nr nx (w2i size) /\
    subnry_disjoint offset nr ny (w2i size) /\
    data nr = data nx /\
    data nx = data ny /\
    writable nr = T`;

val subnry_rebased_snapshot_def = Define `
  subnry_rebased_snapshot
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (fresh : 'p)
      (shared : 'p)
      (old : 'p) <=>
    data fresh = data shared /\
    LENGTH (data shared) = LENGTH (data old) /\
    offset fresh = offset old /\
    minimum fresh = minimum old /\
    maximum fresh = maximum old /\
    writable fresh = writable old /\
    zone fresh = zone old`;

val subnry_snapshot_metadata_def = Define `
  subnry_snapshot_metadata
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (fresh : 'p)
      (old : 'p) <=>
    LENGTH (data fresh) = LENGTH (data old) /\
    offset fresh = offset old /\
    minimum fresh = minimum old /\
    maximum fresh = maximum old /\
    writable fresh = writable old /\
    zone fresh = zone old`;

val subnry_wmpn_postcondition_def = Define `
  subnry_wmpn_postcondition
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (size : word32)
      (nr : 'p)
      (nx : 'p)
      (ny : 'p)
      (nr1 : 'p)
      (nx1 : 'p)
      (ny1 : 'p)
      (result : word64) <=>
    subnry_value data offset nr1 (w2i size) -
        subnry_radix_power (w2i size) * &(w2n result) =
      subnry_value data offset nx (w2i size) -
        subnry_value data offset ny (w2i size) /\
    ((0 : int) <= &(w2n result) /\ &(w2n result) <= (1 : int)) /\
    (!j : int.
       j < offset nr1 \/ offset nr1 + w2i size <= j ==>
       subnry_pelts data nr1 j = subnry_pelts data nr j) /\
    (offset nr1 = offset nx1 \/
     subnry_map_eq_sub
       data nx1 nx (offset nx1) (offset nx1 + w2i size)) /\
    (offset nr1 = offset ny1 \/
     subnry_map_eq_sub
       data ny1 ny (offset ny1) (offset ny1 + w2i size))`;

val subnry_close_precondition_def = Define `
  subnry_close_precondition
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (y1 : 'p)
      (x1 : 'p)
      (nr1 : 'p)
      (ny1 : 'p)
      (nx1 : 'p)
      (m : 'm) <=>
    writable y1 = T /\
    writable nr1 = T /\
    ok m = T /\
    (0 : int) <= w2i size /\
    w2i size <= w2i size /\
    subnry_identical data offset minimum maximum zone nr1 ny1 /\
    subnry_nonoverlap offset ny1 nx1 (w2i size) /\
    zx m = zone y1 /\
    zy m = zone x1 /\
    lx m = size /\
    ly m = size`;

val subnry_same_alias_memory_def = Define `
  subnry_same_alias_memory
      (zr : 'm -> 'z)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (mr : 'm -> word32)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (lr : 'm -> word32)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (left : 'm)
      (right : 'm) <=>
    zr left = zr right /\
    zx left = zx right /\
    zy left = zy right /\
    mr left = mr right /\
    mx left = mx right /\
    my left = my right /\
    lr left = lr right /\
    lx left = lx right /\
    ly left = ly right`;

val subnry_close_intermediate_def = Define `
  subnry_close_intermediate
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (size : word32)
      (m1 : 'm)
      (nx1 : 'p)
      (ny1 : 'p)
      (nx2 : 'p)
      (ny2 : 'p)
      (y1 : 'p)
      (x1 : 'p)
      (y2 : 'p)
      (x2 : 'p) <=>
    maximum y2 = w2i (mx m1) /\
    maximum x2 = w2i (my m1) /\
    subnry_map_eq_sub_shift
      data ny1 y2 (offset ny2) (offset y2) (w2i size) /\
    subnry_map_eq_sub_shift
      data nx1 x2 (offset nx2) (offset x2) (w2i size) /\
    (!j : int.
       j < offset y2 \/ offset y2 + w2i size <= j ==>
       subnry_pelts data y2 j = subnry_pelts data y1 j) /\
    (!j : int.
       j < offset x2 \/ offset x2 + w2i size <= j ==>
       subnry_pelts data x2 j = subnry_pelts data x1 j) /\
    subnry_plength data y2 = subnry_plength data y1 /\
    subnry_plength data x2 = subnry_plength data x1 /\
    minimum y2 = minimum y1 /\
    minimum x2 = minimum x1`;

val subnry_final_postcondition_def = Define `
  subnry_final_postcondition
      (data : 'p -> word64 list)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (size : word32)
      (x : 'p)
      (y : 'p)
      (x2 : 'p)
      (y2 : 'p)
      (result : word64) <=>
    subnry_value data offset y2 (w2i size) -
        subnry_radix_power (w2i size) * &(w2n result) =
      subnry_value data offset x (w2i size) -
        subnry_value data offset y (w2i size) /\
    ((0 : int) <= &(w2n result) /\ &(w2n result) <= (1 : int)) /\
    (!j : int.
       j < offset y2 \/ offset y2 + w2i size <= j ==>
       subnry_pelts data y2 j = subnry_pelts data y j) /\
    (!j : int.
       subnry_pelts data x2 j = subnry_pelts data x j) /\
    subnry_value data offset x2 (w2i size) =
      subnry_value data offset x (w2i size) /\
    minimum x2 = minimum x /\
    maximum x2 = maximum x /\
    subnry_plength data x2 = subnry_plength data x /\
    minimum y2 = minimum y /\
    maximum y2 = maximum y /\
    subnry_plength data y2 = subnry_plength data y`;

val sub_Sub_sub_n_ry_vc =
  ``!data : 'p -> word64 list.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !zr zx zy : 'm -> 'z.
    !mr mx my lr lx ly : 'm -> word32.
    !ok : 'm -> bool.
    !size : word32.
    !x y : 'p.
      (0 : int) <= w2i size ==>
      subnry_valid data offset minimum maximum x (w2i size) ==>
      subnry_valid data offset minimum maximum y (w2i size) ==>
      writable y = T ==>
      subnry_valid data offset minimum maximum y (w2i size) /\
      subnry_valid data offset minimum maximum x (w2i size) /\
      (0 : int) <= w2i size /\
      w2i size <= w2i size /\
      writable y = T /\
      (!y1 x1 : 'p.
         subnry_same_offset_writable_zone
           offset writable zone y1 y ==>
         subnry_same_offset_writable_zone
           offset writable zone x1 x ==>
         (!nr ny nx : 'p.
          !m : 'm.
            subnry_open_precondition
              data offset minimum maximum writable zone
              zx zy mx my lx ly ok size x y y1 x1 nr ny nx m ==>
            subnry_call_precondition
              data offset minimum maximum writable size nr nx ny /\
            (!nx1 ny1 nr1 : 'p.
               subnry_rebased_snapshot
                 data offset minimum maximum writable zone nx1 nr1 nx ==>
               subnry_rebased_snapshot
                 data offset minimum maximum writable zone ny1 nr1 ny ==>
               subnry_snapshot_metadata
                 data offset minimum maximum writable zone nr1 nr ==>
               (!result : word64.
                  subnry_wmpn_postcondition
                    data offset size nr nx ny nr1 nx1 ny1 result ==>
                  subnry_close_precondition
                    data offset minimum maximum writable zone
                    zx zy lx ly ok size y1 x1 nr1 ny1 nx1 m /\
                  (!m1 : 'm.
                   !nx2 ny2 y2 x2 : 'p.
                     subnry_same_alias_memory
                       zr zx zy mr mx my lr lx ly m1 m ==>
                     subnry_same_offset_writable_zone
                       offset writable zone nx2 nx1 ==>
                     subnry_same_offset_writable_zone
                       offset writable zone ny2 ny1 ==>
                     subnry_same_offset_minimum_writable_zone
                       offset minimum writable zone y2 y1 ==>
                     subnry_same_offset_minimum_writable_zone
                       offset minimum writable zone x2 x1 ==>
                     subnry_close_intermediate
                       data offset minimum maximum mx my size m1
                       nx1 ny1 nx2 ny2 y1 x1 y2 x2 ==>
                     subnry_final_postcondition
                       data offset minimum maximum
                       size x y x2 y2 result)))))``;
