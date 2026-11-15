(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/sub_Sub_sub_rxqtvc: the verification condition for
  multiprecision subtraction of a shorter value from a longer value in the
  first operand, including borrow arithmetic, pointer validity, alias
  separation, memory framing, and preservation of pointer metadata. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

Datatype:
  subrx_ptr =
    SubRxPtr (int -> word64) num int int int bool 'zone
End

Datatype:
  subrx_mem =
    SubRxMem 'zone 'zone 'zone
      word32 word32 word32 word32 word32 word32 bool
End

val subrx_data_def = Define `
  subrx_data
      (SubRxPtr data data_length offset minimum maximum writable zone) =
    data`;

val subrx_data_length_def = Define `
  subrx_data_length
      (SubRxPtr data data_length offset minimum maximum writable zone) =
    data_length`;

val subrx_offset_def = Define `
  subrx_offset
      (SubRxPtr data data_length offset minimum maximum writable zone) =
    offset`;

val subrx_minimum_def = Define `
  subrx_minimum
      (SubRxPtr data data_length offset minimum maximum writable zone) =
    minimum`;

val subrx_maximum_def = Define `
  subrx_maximum
      (SubRxPtr data data_length offset minimum maximum writable zone) =
    maximum`;

val subrx_writable_def = Define `
  subrx_writable
      (SubRxPtr data data_length offset minimum maximum writable zone) =
    writable`;

val subrx_zone_def = Define `
  subrx_zone
      (SubRxPtr data data_length offset minimum maximum writable zone) =
    zone`;

val subrx_zr_def = Define `
  subrx_zr
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    zr`;

val subrx_zx_def = Define `
  subrx_zx
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    zx`;

val subrx_zy_def = Define `
  subrx_zy
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    zy`;

val subrx_mr_def = Define `
  subrx_mr
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    mr`;

val subrx_mx_def = Define `
  subrx_mx
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    mx`;

val subrx_my_def = Define `
  subrx_my
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    my`;

val subrx_lr_def = Define `
  subrx_lr
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    lr`;

val subrx_lx_def = Define `
  subrx_lx
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    lx`;

val subrx_ly_def = Define `
  subrx_ly
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    ly`;

val subrx_ok_def = Define `
  subrx_ok
      (SubRxMem zr zx zy mr mx my lr lx ly ok) =
    ok`;

val subrx_radix_def = Define `
  subrx_radix = (18446744073709551616 : int)`;

val subrx_to_num_def = Define `
  subrx_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val subrx_int32_in_bounds_def = Define `
  subrx_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val subrx_pelts_def = Define `
  subrx_pelts (p : 'zone subrx_ptr) (index : int) =
    subrx_data p index`;

val subrx_plength_def = Define `
  subrx_plength (p : 'zone subrx_ptr) =
    &(subrx_data_length p)`;

val subrx_valid_def = Define `
  subrx_valid (p : 'zone subrx_ptr) (size : int) <=>
    subrx_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= subrx_minimum p /\
     subrx_minimum p <= subrx_offset p) /\
    subrx_offset p + size <= subrx_maximum p /\
    subrx_maximum p <= subrx_plength p`;

val subrx_radix_power_def = Define `
  subrx_radix_power (exponent : int) =
    subrx_radix ** subrx_to_num exponent`;

val subrx_value_from_def = Define `
  (subrx_value_from
      (p : 'zone subrx_ptr) (index : int) 0 =
     (0 : int)) /\
  (subrx_value_from p index (SUC count) =
     &(w2n (subrx_pelts p index)) +
       subrx_radix *
         subrx_value_from p (index + (1 : int)) count)`;

val subrx_value_def = Define `
  subrx_value (p : 'zone subrx_ptr) (size : int) =
    subrx_value_from
      p (subrx_offset p) (subrx_to_num size)`;

val subrx_map_eq_sub_def = Define `
  subrx_map_eq_sub
      (left : 'zone subrx_ptr)
      (right : 'zone subrx_ptr)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      subrx_pelts left i = subrx_pelts right i`;

val subrx_map_eq_sub_shift_def = Define `
  subrx_map_eq_sub_shift
      (left : 'zone subrx_ptr)
      (right : 'zone subrx_ptr)
      (left_offset : int)
      (right_offset : int)
      (size : int) <=>
    !i : int.
      (0 : int) <= i /\ i < size ==>
      subrx_pelts left (left_offset + i) =
        subrx_pelts right (right_offset + i)`;

val subrx_same_pelts_def = Define `
  subrx_same_pelts
      (left : 'zone subrx_ptr)
      (right : 'zone subrx_ptr) <=>
    !i : int.
      subrx_pelts left i = subrx_pelts right i`;

val subrx_same_data_def = Define `
  subrx_same_data
      (left : 'zone subrx_ptr)
      (right : 'zone subrx_ptr) <=>
    subrx_data_length left = subrx_data_length right /\
    subrx_same_pelts left right`;

val subrx_identical_def = Define `
  subrx_identical
      (left : 'zone subrx_ptr)
      (right : 'zone subrx_ptr) <=>
    subrx_same_data left right /\
    subrx_offset left = subrx_offset right /\
    subrx_minimum left = subrx_minimum right /\
    subrx_maximum left = subrx_maximum right /\
    subrx_zone left = subrx_zone right`;

val subrx_same_offset_writable_zone_def = Define `
  subrx_same_offset_writable_zone
      (left : 'zone subrx_ptr)
      (right : 'zone subrx_ptr) <=>
    subrx_offset left = subrx_offset right /\
    subrx_writable left = subrx_writable right /\
    subrx_zone left = subrx_zone right`;

val subrx_same_offset_minimum_writable_zone_def = Define `
  subrx_same_offset_minimum_writable_zone
      (left : 'zone subrx_ptr)
      (right : 'zone subrx_ptr) <=>
    subrx_offset left = subrx_offset right /\
    subrx_minimum left = subrx_minimum right /\
    subrx_writable left = subrx_writable right /\
    subrx_zone left = subrx_zone right`;

val subrx_disjoint_def = Define `
  subrx_disjoint
      (left : 'zone subrx_ptr)
      (left_size : int)
      (right : 'zone subrx_ptr)
      (right_size : int) <=>
    subrx_offset left = subrx_offset right \/
    subrx_offset left + left_size <= subrx_offset right \/
    subrx_offset right + right_size <= subrx_offset left`;

val subrx_nonoverlap_def = Define `
  subrx_nonoverlap
      (left : 'zone subrx_ptr)
      (left_size : int)
      (right : 'zone subrx_ptr)
      (right_size : int) <=>
    ((0 : int) <= subrx_offset left /\
     subrx_offset left + left_size <= subrx_offset right) \/
    ((0 : int) <= subrx_offset right /\
     subrx_offset right + right_size <= subrx_offset left)`;

val subrx_open_precondition_def = Define `
  subrx_open_precondition
      (sy : word32)
      (sx : word32)
      (x : 'zone subrx_ptr)
      (y : 'zone subrx_ptr)
      (y1 : 'zone subrx_ptr)
      (x1 : 'zone subrx_ptr)
      (nr : 'zone subrx_ptr)
      (nx : 'zone subrx_ptr)
      (ny : 'zone subrx_ptr)
      (m : 'zone subrx_mem) <=>
    subrx_writable nr = T /\
    subrx_value nx (w2i sx) = subrx_value x (w2i sx) /\
    subrx_value ny (w2i sy) = subrx_value y (w2i sy) /\
    subrx_valid nx (w2i sx) /\
    subrx_valid ny (w2i sy) /\
    subrx_identical nr nx /\
    subrx_nonoverlap nx (w2i sx) ny (w2i sy) /\
    subrx_zx m = subrx_zone x1 /\
    subrx_zy m = subrx_zone y1 /\
    w2i (subrx_mx m) = subrx_maximum x /\
    w2i (subrx_my m) = subrx_maximum y /\
    subrx_lx m = sx /\
    subrx_ly m = sy /\
    subrx_ok m = T /\
    subrx_map_eq_sub_shift
      nx x1 (subrx_offset nx) (subrx_offset x1) (w2i sx) /\
    subrx_map_eq_sub_shift
      ny y1 (subrx_offset ny) (subrx_offset y1) (w2i sy) /\
    subrx_same_pelts x1 x /\
    subrx_same_pelts y1 y /\
    subrx_plength x1 = subrx_plength x /\
    subrx_plength y1 = subrx_plength y /\
    subrx_minimum x1 = subrx_minimum x /\
    subrx_minimum y1 = subrx_minimum y /\
    subrx_same_data nr nx /\
    subrx_same_data nx ny`;

val subrx_call_precondition_def = Define `
  subrx_call_precondition
      (sy : word32)
      (sx : word32)
      (nr : 'zone subrx_ptr)
      (nx : 'zone subrx_ptr)
      (ny : 'zone subrx_ptr) <=>
    (0 : int) <= w2i sy /\
    w2i sy <= w2i sx /\
    subrx_valid nr (w2i sx) /\
    subrx_valid nx (w2i sx) /\
    subrx_valid ny (w2i sy) /\
    subrx_disjoint nr (w2i sx) nx (w2i sx) /\
    subrx_disjoint nr (w2i sx) ny (w2i sy) /\
    subrx_same_data nr nx /\
    subrx_same_data nx ny /\
    subrx_writable nr = T`;

val subrx_rebased_snapshot_def = Define `
  subrx_rebased_snapshot
      (fresh : 'zone subrx_ptr)
      (shared : 'zone subrx_ptr)
      (old : 'zone subrx_ptr) <=>
    subrx_same_data fresh shared /\
    subrx_data_length shared = subrx_data_length old /\
    subrx_offset fresh = subrx_offset old /\
    subrx_minimum fresh = subrx_minimum old /\
    subrx_maximum fresh = subrx_maximum old /\
    subrx_writable fresh = subrx_writable old /\
    subrx_zone fresh = subrx_zone old`;

val subrx_snapshot_metadata_def = Define `
  subrx_snapshot_metadata
      (fresh : 'zone subrx_ptr)
      (old : 'zone subrx_ptr) <=>
    subrx_data_length fresh = subrx_data_length old /\
    subrx_offset fresh = subrx_offset old /\
    subrx_minimum fresh = subrx_minimum old /\
    subrx_maximum fresh = subrx_maximum old /\
    subrx_writable fresh = subrx_writable old /\
    subrx_zone fresh = subrx_zone old`;

val subrx_wmpn_postcondition_def = Define `
  subrx_wmpn_postcondition
      (sy : word32)
      (sx : word32)
      (nr : 'zone subrx_ptr)
      (nx : 'zone subrx_ptr)
      (ny : 'zone subrx_ptr)
      (nr1 : 'zone subrx_ptr)
      (nx1 : 'zone subrx_ptr)
      (ny1 : 'zone subrx_ptr)
      (result : word64) <=>
    subrx_value nr1 (w2i sx) -
        subrx_radix_power (w2i sx) * &(w2n result) =
      subrx_value nx (w2i sx) -
        subrx_value ny (w2i sy) /\
    ((0 : int) <= &(w2n result) /\ &(w2n result) <= (1 : int)) /\
    (!j : int.
       j < subrx_offset nr1 \/ subrx_offset nr1 + w2i sx <= j ==>
       subrx_pelts nr1 j = subrx_pelts nr j) /\
    (subrx_offset nr1 = subrx_offset nx1 \/
     subrx_map_eq_sub
       nx1 nx (subrx_offset nx1) (subrx_offset nx1 + w2i sx)) /\
    (subrx_offset nr1 = subrx_offset ny1 \/
     subrx_map_eq_sub
       ny1 ny (subrx_offset ny1) (subrx_offset ny1 + w2i sy))`;

val subrx_close_precondition_def = Define `
  subrx_close_precondition
      (sy : word32)
      (sx : word32)
      (x1 : 'zone subrx_ptr)
      (y1 : 'zone subrx_ptr)
      (nr1 : 'zone subrx_ptr)
      (nx1 : 'zone subrx_ptr)
      (ny1 : 'zone subrx_ptr)
      (m : 'zone subrx_mem) <=>
    subrx_writable x1 = T /\
    subrx_writable nr1 = T /\
    subrx_ok m = T /\
    (0 : int) <= w2i sy /\
    w2i sy <= w2i sx /\
    subrx_identical nr1 nx1 /\
    subrx_nonoverlap nx1 (w2i sx) ny1 (w2i sy) /\
    subrx_zx m = subrx_zone x1 /\
    subrx_zy m = subrx_zone y1 /\
    subrx_lx m = sx /\
    subrx_ly m = sy`;

val subrx_same_alias_memory_def = Define `
  subrx_same_alias_memory
      (left : 'zone subrx_mem)
      (right : 'zone subrx_mem) <=>
    subrx_zr left = subrx_zr right /\
    subrx_zx left = subrx_zx right /\
    subrx_zy left = subrx_zy right /\
    subrx_mr left = subrx_mr right /\
    subrx_mx left = subrx_mx right /\
    subrx_my left = subrx_my right /\
    subrx_lr left = subrx_lr right /\
    subrx_lx left = subrx_lx right /\
    subrx_ly left = subrx_ly right`;

val subrx_close_intermediate_def = Define `
  subrx_close_intermediate
      (sy : word32)
      (sx : word32)
      (m1 : 'zone subrx_mem)
      (nx1 : 'zone subrx_ptr)
      (ny1 : 'zone subrx_ptr)
      (nx2 : 'zone subrx_ptr)
      (ny2 : 'zone subrx_ptr)
      (x1 : 'zone subrx_ptr)
      (y1 : 'zone subrx_ptr)
      (x2 : 'zone subrx_ptr)
      (y2 : 'zone subrx_ptr) <=>
    subrx_maximum x2 = w2i (subrx_mx m1) /\
    subrx_maximum y2 = w2i (subrx_my m1) /\
    subrx_map_eq_sub_shift
      nx1 x2 (subrx_offset nx2) (subrx_offset x2) (w2i sx) /\
    subrx_map_eq_sub_shift
      ny1 y2 (subrx_offset ny2) (subrx_offset y2) (w2i sy) /\
    (!j : int.
       j < subrx_offset x2 \/ subrx_offset x2 + w2i sx <= j ==>
       subrx_pelts x2 j = subrx_pelts x1 j) /\
    (!j : int.
       j < subrx_offset y2 \/ subrx_offset y2 + w2i sy <= j ==>
       subrx_pelts y2 j = subrx_pelts y1 j) /\
    subrx_plength x2 = subrx_plength x1 /\
    subrx_plength y2 = subrx_plength y1 /\
    subrx_minimum x2 = subrx_minimum x1 /\
    subrx_minimum y2 = subrx_minimum y1`;

val subrx_final_postcondition_def = Define `
  subrx_final_postcondition
      (sy : word32)
      (sx : word32)
      (x : 'zone subrx_ptr)
      (y : 'zone subrx_ptr)
      (x2 : 'zone subrx_ptr)
      (y2 : 'zone subrx_ptr)
      (result : word64) <=>
    subrx_value x2 (w2i sx) -
        subrx_radix_power (w2i sx) * &(w2n result) =
      subrx_value x (w2i sx) -
        subrx_value y (w2i sy) /\
    ((0 : int) <= &(w2n result) /\ &(w2n result) <= (1 : int)) /\
    (!j : int.
       j < subrx_offset x2 \/ subrx_offset x2 + w2i sx <= j ==>
       subrx_pelts x2 j = subrx_pelts x j) /\
    (!j : int.
       subrx_pelts y2 j = subrx_pelts y j) /\
    subrx_value y2 (w2i sy) = subrx_value y (w2i sy) /\
    subrx_minimum x2 = subrx_minimum x /\
    subrx_maximum x2 = subrx_maximum x /\
    subrx_plength x2 = subrx_plength x /\
    subrx_minimum y2 = subrx_minimum y /\
    subrx_maximum y2 = subrx_maximum y /\
    subrx_plength y2 = subrx_plength y`;

val sub_Sub_sub_rx_vc =
  ``!sy sx : word32.
    !x y : 'zone subrx_ptr.
      (0 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      subrx_valid x (w2i sx) ==>
      subrx_valid y (w2i sy) ==>
      subrx_writable x = T ==>
      subrx_valid x (w2i sx) /\
      subrx_valid y (w2i sy) /\
      (0 : int) <= w2i sy /\
      w2i sy <= w2i sx /\
      subrx_writable x = T /\
      (!y1 x1 : 'zone subrx_ptr.
         subrx_same_offset_writable_zone y1 y ==>
         subrx_same_offset_writable_zone x1 x ==>
         (!nr nx ny : 'zone subrx_ptr.
          !m : 'zone subrx_mem.
            subrx_open_precondition
              sy sx x y y1 x1 nr nx ny m ==>
            subrx_call_precondition sy sx nr nx ny /\
            (!ny1 nx1 nr1 : 'zone subrx_ptr.
               subrx_rebased_snapshot ny1 nr1 ny ==>
               subrx_rebased_snapshot nx1 nr1 nx ==>
               subrx_snapshot_metadata nr1 nr ==>
               (!result : word64.
                  subrx_wmpn_postcondition
                    sy sx nr nx ny nr1 nx1 ny1 result ==>
                  subrx_close_precondition
                    sy sx x1 y1 nr1 nx1 ny1 m /\
                  (!m1 : 'zone subrx_mem.
                   !ny2 nx2 y2 x2 : 'zone subrx_ptr.
                     subrx_same_alias_memory m1 m ==>
                     subrx_same_offset_writable_zone ny2 ny1 ==>
                     subrx_same_offset_writable_zone nx2 nx1 ==>
                     subrx_same_offset_minimum_writable_zone y2 y1 ==>
                     subrx_same_offset_minimum_writable_zone x2 x1 ==>
                     subrx_close_intermediate
                       sy sx m1 nx1 ny1 nx2 ny2 x1 y1 x2 y2 ==>
                     subrx_final_postcondition
                       sy sx x y x2 y2 result)))))``;
