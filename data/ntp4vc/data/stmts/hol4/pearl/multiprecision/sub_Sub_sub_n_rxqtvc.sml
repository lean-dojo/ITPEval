(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_sub_n_rxqtvc: the verification condition for
  equal-length multiprecision subtraction into the first operand, including
  borrow arithmetic, pointer validity, alias separation, memory framing, and
  preservation of pointer metadata. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val subnrx_radix_def = Define `
  subnrx_radix = (18446744073709551616 : int)`;

val subnrx_to_num_def = Define `
  subnrx_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val subnrx_int32_in_bounds_def = Define `
  subnrx_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val subnrx_plength_def = Define `
  subnrx_plength (data_length : 'p -> num) (p : 'p) =
    &(data_length p)`;

val subnrx_valid_def = Define `
  subnrx_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (size : int) <=>
    subnrx_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + size <= maximum p /\
    maximum p <= subnrx_plength data_length p`;

val subnrx_radix_power_def = Define `
  subnrx_radix_power (exponent : int) =
    subnrx_radix ** subnrx_to_num exponent`;

val subnrx_value_from_def = Define `
  (subnrx_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (subnrx_value_from pelts p index (SUC count) =
     &(w2n (pelts p index)) +
       subnrx_radix *
         subnrx_value_from pelts p (index + (1 : int)) count)`;

val subnrx_value_def = Define `
  subnrx_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (size : int) =
    subnrx_value_from
      pelts p (offset p) (subnrx_to_num size)`;

val subnrx_map_eq_sub_def = Define `
  subnrx_map_eq_sub
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      pelts left i = pelts right i`;

val subnrx_map_eq_sub_shift_def = Define `
  subnrx_map_eq_sub_shift
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

val subnrx_same_pelts_def = Define `
  subnrx_same_pelts
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    !i : int.
      pelts left i = pelts right i`;

val subnrx_same_data_def = Define `
  subnrx_same_data
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    subnrx_same_pelts pelts left right`;

val subnrx_identical_def = Define `
  subnrx_identical
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (zone : 'p -> 'z)
      (left : 'p)
      (right : 'p) <=>
    subnrx_same_data data_length pelts left right /\
    offset left = offset right /\
    minimum left = minimum right /\
    maximum left = maximum right /\
    zone left = zone right`;

val subnrx_same_offset_writable_zone_def = Define `
  subnrx_same_offset_writable_zone
      (offset : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (left : 'p)
      (right : 'p) <=>
    offset left = offset right /\
    writable left = writable right /\
    zone left = zone right`;

val subnrx_same_offset_minimum_writable_zone_def = Define `
  subnrx_same_offset_minimum_writable_zone
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

val subnrx_disjoint_def = Define `
  subnrx_disjoint
      (offset : 'p -> int)
      (left : 'p)
      (right : 'p)
      (size : int) <=>
    offset left = offset right \/
    offset left + size <= offset right \/
    offset right + size <= offset left`;

val subnrx_nonoverlap_def = Define `
  subnrx_nonoverlap
      (offset : 'p -> int)
      (left : 'p)
      (right : 'p)
      (size : int) <=>
    ((0 : int) <= offset left /\
     offset left + size <= offset right) \/
    ((0 : int) <= offset right /\
     offset right + size <= offset left)`;

val subnrx_open_precondition_def = Define `
  subnrx_open_precondition
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
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
      (nx : 'p)
      (ny : 'p)
      (m : 'm) <=>
    writable nr = T /\
    subnrx_value pelts offset nx (w2i size) =
      subnrx_value pelts offset x (w2i size) /\
    subnrx_value pelts offset ny (w2i size) =
      subnrx_value pelts offset y (w2i size) /\
    subnrx_valid data_length offset minimum maximum nx (w2i size) /\
    subnrx_valid data_length offset minimum maximum ny (w2i size) /\
    subnrx_identical
      data_length pelts offset minimum maximum zone nr nx /\
    subnrx_nonoverlap offset nx ny (w2i size) /\
    zx m = zone x1 /\
    zy m = zone y1 /\
    w2i (mx m) = maximum x /\
    w2i (my m) = maximum y /\
    lx m = size /\
    ly m = size /\
    ok m = T /\
    subnrx_map_eq_sub_shift
      pelts nx x1 (offset nx) (offset x1) (w2i size) /\
    subnrx_map_eq_sub_shift
      pelts ny y1 (offset ny) (offset y1) (w2i size) /\
    subnrx_same_pelts pelts x1 x /\
    subnrx_same_pelts pelts y1 y /\
    subnrx_plength data_length x1 = subnrx_plength data_length x /\
    subnrx_plength data_length y1 = subnrx_plength data_length y /\
    minimum x1 = minimum x /\
    minimum y1 = minimum y /\
    subnrx_same_data data_length pelts nr nx /\
    subnrx_same_data data_length pelts nx ny`;

val subnrx_call_precondition_def = Define `
  subnrx_call_precondition
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (pelts : 'p -> int -> word64)
      (size : word32)
      (nr : 'p)
      (nx : 'p)
      (ny : 'p) <=>
    (0 : int) <= w2i size /\
    subnrx_valid data_length offset minimum maximum nr (w2i size) /\
    subnrx_valid data_length offset minimum maximum nx (w2i size) /\
    subnrx_valid data_length offset minimum maximum ny (w2i size) /\
    subnrx_disjoint offset nr nx (w2i size) /\
    subnrx_disjoint offset nr ny (w2i size) /\
    subnrx_same_data data_length pelts nr nx /\
    subnrx_same_data data_length pelts nx ny /\
    writable nr = T`;

val subnrx_rebased_snapshot_def = Define `
  subnrx_rebased_snapshot
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
    subnrx_same_data data_length pelts fresh shared /\
    data_length shared = data_length old /\
    offset fresh = offset old /\
    minimum fresh = minimum old /\
    maximum fresh = maximum old /\
    writable fresh = writable old /\
    zone fresh = zone old`;

val subnrx_snapshot_metadata_def = Define `
  subnrx_snapshot_metadata
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

val subnrx_wmpn_postcondition_def = Define `
  subnrx_wmpn_postcondition
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
    subnrx_value pelts offset nr1 (w2i size) -
        subnrx_radix_power (w2i size) * &(w2n result) =
      subnrx_value pelts offset nx (w2i size) -
        subnrx_value pelts offset ny (w2i size) /\
    ((0 : int) <= &(w2n result) /\ &(w2n result) <= (1 : int)) /\
    (!j : int.
       j < offset nr1 \/ offset nr1 + w2i size <= j ==>
       pelts nr1 j = pelts nr j) /\
    (offset nr1 = offset nx1 \/
     subnrx_map_eq_sub
       pelts nx1 nx (offset nx1) (offset nx1 + w2i size)) /\
    (offset nr1 = offset ny1 \/
     subnrx_map_eq_sub
       pelts ny1 ny (offset ny1) (offset ny1 + w2i size))`;

val subnrx_close_precondition_def = Define `
  subnrx_close_precondition
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (pelts : 'p -> int -> word64)
      (zx : 'm -> 'z)
      (zy : 'm -> 'z)
      (lx : 'm -> word32)
      (ly : 'm -> word32)
      (ok : 'm -> bool)
      (size : word32)
      (x1 : 'p)
      (y1 : 'p)
      (nr1 : 'p)
      (nx1 : 'p)
      (ny1 : 'p)
      (m : 'm) <=>
    writable x1 = T /\
    writable nr1 = T /\
    ok m = T /\
    (0 : int) <= w2i size /\
    w2i size <= w2i size /\
    subnrx_identical
      data_length pelts offset minimum maximum zone nr1 nx1 /\
    subnrx_nonoverlap offset nx1 ny1 (w2i size) /\
    zx m = zone x1 /\
    zy m = zone y1 /\
    lx m = size /\
    ly m = size`;

val subnrx_same_alias_memory_def = Define `
  subnrx_same_alias_memory
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

val subnrx_close_intermediate_def = Define `
  subnrx_close_intermediate
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
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
      (x1 : 'p)
      (y1 : 'p)
      (x2 : 'p)
      (y2 : 'p) <=>
    maximum x2 = w2i (mx m1) /\
    maximum y2 = w2i (my m1) /\
    subnrx_map_eq_sub_shift
      pelts nx1 x2 (offset nx2) (offset x2) (w2i size) /\
    subnrx_map_eq_sub_shift
      pelts ny1 y2 (offset ny2) (offset y2) (w2i size) /\
    (!j : int.
       j < offset x2 \/ offset x2 + w2i size <= j ==>
       pelts x2 j = pelts x1 j) /\
    (!j : int.
       j < offset y2 \/ offset y2 + w2i size <= j ==>
       pelts y2 j = pelts y1 j) /\
    subnrx_plength data_length x2 =
      subnrx_plength data_length x1 /\
    subnrx_plength data_length y2 =
      subnrx_plength data_length y1 /\
    minimum x2 = minimum x1 /\
    minimum y2 = minimum y1`;

val subnrx_final_postcondition_def = Define `
  subnrx_final_postcondition
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (size : word32)
      (x : 'p)
      (y : 'p)
      (x2 : 'p)
      (y2 : 'p)
      (result : word64) <=>
    subnrx_value pelts offset x2 (w2i size) -
        subnrx_radix_power (w2i size) * &(w2n result) =
      subnrx_value pelts offset x (w2i size) -
        subnrx_value pelts offset y (w2i size) /\
    ((0 : int) <= &(w2n result) /\ &(w2n result) <= (1 : int)) /\
    (!j : int.
       j < offset x2 \/ offset x2 + w2i size <= j ==>
       pelts x2 j = pelts x j) /\
    (!j : int.
       pelts y2 j = pelts y j) /\
    subnrx_value pelts offset y2 (w2i size) =
      subnrx_value pelts offset y (w2i size) /\
    minimum x2 = minimum x /\
    maximum x2 = maximum x /\
    subnrx_plength data_length x2 =
      subnrx_plength data_length x /\
    minimum y2 = minimum y /\
    maximum y2 = maximum y /\
    subnrx_plength data_length y2 =
      subnrx_plength data_length y`;

val sub_Sub_sub_n_rx_vc =
  ``!data_length : 'p -> num.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !pelts : 'p -> int -> word64.
    !zr zx zy : 'm -> 'z.
    !mr mx my lr lx ly : 'm -> word32.
    !ok : 'm -> bool.
    !size : word32.
    !x y : 'p.
      (0 : int) <= w2i size ==>
      subnrx_valid data_length offset minimum maximum x (w2i size) ==>
      subnrx_valid data_length offset minimum maximum y (w2i size) ==>
      writable x = T ==>
      subnrx_valid data_length offset minimum maximum x (w2i size) /\
      subnrx_valid data_length offset minimum maximum y (w2i size) /\
      (0 : int) <= w2i size /\
      w2i size <= w2i size /\
      writable x = T /\
      (!y1 x1 : 'p.
         subnrx_same_offset_writable_zone
           offset writable zone y1 y ==>
         subnrx_same_offset_writable_zone
           offset writable zone x1 x ==>
         (!nr nx ny : 'p.
          !m : 'm.
            subnrx_open_precondition
              data_length offset minimum maximum writable zone pelts
              zx zy mx my lx ly ok size x y y1 x1 nr nx ny m ==>
            subnrx_call_precondition
              data_length offset minimum maximum writable pelts
              size nr nx ny /\
            (!ny1 nx1 nr1 : 'p.
               subnrx_rebased_snapshot
                 data_length pelts offset minimum maximum writable zone
                 ny1 nr1 ny ==>
               subnrx_rebased_snapshot
                 data_length pelts offset minimum maximum writable zone
                 nx1 nr1 nx ==>
               subnrx_snapshot_metadata
                 data_length offset minimum maximum writable zone nr1 nr ==>
               (!result : word64.
                  subnrx_wmpn_postcondition
                    pelts offset size nr nx ny nr1 nx1 ny1 result ==>
                  subnrx_close_precondition
                    data_length offset minimum maximum writable zone pelts
                    zx zy lx ly ok size x1 y1 nr1 nx1 ny1 m /\
                  (!m1 : 'm.
                   !ny2 nx2 y2 x2 : 'p.
                     subnrx_same_alias_memory
                       zr zx zy mr mx my lr lx ly m1 m ==>
                     subnrx_same_offset_writable_zone
                       offset writable zone ny2 ny1 ==>
                     subnrx_same_offset_writable_zone
                       offset writable zone nx2 nx1 ==>
                     subnrx_same_offset_minimum_writable_zone
                       offset minimum writable zone y2 y1 ==>
                     subnrx_same_offset_minimum_writable_zone
                       offset minimum writable zone x2 x1 ==>
                     subnrx_close_intermediate
                       data_length pelts offset minimum maximum mx my size m1
                       nx1 ny1 nx2 ny2 x1 y1 x2 y2 ==>
                     subnrx_final_postcondition
                       data_length pelts offset minimum maximum
                       size x y x2 y2 result)))))``;
