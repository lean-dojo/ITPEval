(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/add_Add_add_ryqtvc: the verification condition for
  adding two multiprecision values of possibly different lengths into the
  second operand, including carry, pointer validity, alias separation,
  memory framing, and preservation of pointer metadata. This file contains
  no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val addry_radix_def = Define `
  addry_radix = (18446744073709551616 : int)`;

val addry_to_num_def = Define `
  addry_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val addry_int32_in_bounds_def = Define `
  addry_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val addry_plength_def = Define `
  addry_plength (data_length : 'p -> num) (p : 'p) =
    &(data_length p)`;

val addry_valid_def = Define `
  addry_valid
      (data_length : 'p -> num)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (p : 'p)
      (size : int) <=>
    addry_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= minimum p /\ minimum p <= offset p) /\
    offset p + size <= maximum p /\
    maximum p <= addry_plength data_length p`;

val addry_radix_power_def = Define `
  addry_radix_power (exponent : int) =
    addry_radix ** addry_to_num exponent`;

val addry_value_from_def = Define `
  (addry_value_from
      (pelts : 'p -> int -> word64) (p : 'p) (index : int) 0 =
     (0 : int)) /\
  (addry_value_from pelts p index (SUC count) =
     &(w2n (pelts p index)) +
       addry_radix *
         addry_value_from pelts p (index + (1 : int)) count)`;

val addry_value_def = Define `
  addry_value
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (p : 'p)
      (size : int) =
    addry_value_from
      pelts p (offset p) (addry_to_num size)`;

val addry_map_eq_sub_def = Define `
  addry_map_eq_sub
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p)
      (lower : int)
      (upper : int) <=>
    !i : int.
      lower <= i /\ i < upper ==>
      pelts left i = pelts right i`;

val addry_map_eq_sub_shift_def = Define `
  addry_map_eq_sub_shift
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

val addry_same_pelts_def = Define `
  addry_same_pelts
      (pelts : 'p -> int -> word64) (left : 'p) (right : 'p) <=>
    !i : int.
      pelts left i = pelts right i`;

val addry_same_data_def = Define `
  addry_same_data
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (left : 'p)
      (right : 'p) <=>
    data_length left = data_length right /\
    pelts left = pelts right`;

val addry_identical_def = Define `
  addry_identical
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (zone : 'p -> 'z)
      (left : 'p)
      (right : 'p) <=>
    addry_same_data data_length pelts left right /\
    offset left = offset right /\
    minimum left = minimum right /\
    maximum left = maximum right /\
    zone left = zone right`;

val addry_same_offset_writable_zone_def = Define `
  addry_same_offset_writable_zone
      (offset : 'p -> int)
      (writable : 'p -> bool)
      (zone : 'p -> 'z)
      (left : 'p)
      (right : 'p) <=>
    offset left = offset right /\
    writable left = writable right /\
    zone left = zone right`;

val addry_same_offset_minimum_writable_zone_def = Define `
  addry_same_offset_minimum_writable_zone
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

val addry_disjoint_def = Define `
  addry_disjoint
      (offset : 'p -> int)
      (left : 'p)
      (left_size : int)
      (right : 'p)
      (right_size : int) <=>
    offset left = offset right \/
    offset left + left_size <= offset right \/
    offset right + right_size <= offset left`;

val addry_nonoverlap_def = Define `
  addry_nonoverlap
      (offset : 'p -> int)
      (left : 'p)
      (right : 'p)
      (size : int) <=>
    ((0 : int) <= offset left /\
     offset left + size <= offset right) \/
    ((0 : int) <= offset right /\
     offset right + size <= offset left)`;

val addry_open_precondition_def = Define `
  addry_open_precondition
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
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
      (sx : word32)
      (x : 'p)
      (y : 'p)
      (y1 : 'p)
      (x1 : 'p)
      (nr : 'p)
      (ny : 'p)
      (nx : 'p)
      (m : 'm) <=>
    writable nr = T /\
    addry_value pelts offset ny (w2i sx) =
      addry_value pelts offset y (w2i sx) /\
    addry_value pelts offset nx (w2i sx) =
      addry_value pelts offset x (w2i sx) /\
    addry_valid data_length offset minimum maximum ny (w2i sx) /\
    addry_valid data_length offset minimum maximum nx (w2i sx) /\
    addry_identical
      data_length pelts offset minimum maximum zone nr ny /\
    addry_nonoverlap offset ny nx (w2i sx) /\
    zx m = zone y1 /\
    zy m = zone x1 /\
    w2i (mx m) = maximum y /\
    w2i (my m) = maximum x /\
    lx m = sx /\
    ly m = sx /\
    ok m = T /\
    addry_map_eq_sub_shift
      pelts ny y1 (offset ny) (offset y1) (w2i sx) /\
    addry_map_eq_sub_shift
      pelts nx x1 (offset nx) (offset x1) (w2i sx) /\
    addry_same_pelts pelts y1 y /\
    addry_same_pelts pelts x1 x /\
    addry_plength data_length y1 = addry_plength data_length y /\
    addry_plength data_length x1 = addry_plength data_length x /\
    minimum y1 = minimum y /\
    minimum x1 = minimum x /\
    addry_same_data data_length pelts nr ny /\
    addry_same_data data_length pelts ny nx`;

val addry_call_precondition_def = Define `
  addry_call_precondition
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (writable : 'p -> bool)
      (sy : word32)
      (sx : word32)
      (nr : 'p)
      (ny : 'p)
      (nx : 'p) <=>
    (0 : int) <= w2i sy /\
    w2i sy <= w2i sx /\
    addry_valid data_length offset minimum maximum nr (w2i sx) /\
    addry_valid data_length offset minimum maximum nx (w2i sx) /\
    addry_valid data_length offset minimum maximum ny (w2i sy) /\
    addry_disjoint offset nr (w2i sx) nx (w2i sx) /\
    addry_disjoint offset nr (w2i sx) ny (w2i sy) /\
    addry_same_data data_length pelts nr nx /\
    addry_same_data data_length pelts nx ny /\
    writable nr = T`;

val addry_rebased_snapshot_def = Define `
  addry_rebased_snapshot
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
    addry_same_data data_length pelts fresh shared /\
    data_length shared = data_length old /\
    offset fresh = offset old /\
    minimum fresh = minimum old /\
    maximum fresh = maximum old /\
    writable fresh = writable old /\
    zone fresh = zone old`;

val addry_snapshot_metadata_def = Define `
  addry_snapshot_metadata
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

val addry_wmpn_postcondition_def = Define `
  addry_wmpn_postcondition
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (sy : word32)
      (sx : word32)
      (nr : 'p)
      (ny : 'p)
      (nx : 'p)
      (nr1 : 'p)
      (ny1 : 'p)
      (nx1 : 'p)
      (res : word64) <=>
    addry_value pelts offset nr1 (w2i sx) +
        addry_radix_power (w2i sx) * &(w2n res) =
      addry_value pelts offset nx (w2i sx) +
        addry_value pelts offset ny (w2i sy) /\
    ((0 : int) <= &(w2n res) /\ &(w2n res) <= (1 : int)) /\
    (!j : int.
       j < offset nr1 \/ offset nr1 + w2i sx <= j ==>
       pelts nr1 j = pelts nr j) /\
    (offset nr1 = offset nx1 \/
     addry_map_eq_sub
       pelts nx1 nx (offset nx1) (offset nx1 + w2i sx)) /\
    (offset nr1 = offset ny1 \/
     addry_map_eq_sub
       pelts ny1 ny (offset ny1) (offset ny1 + w2i sy))`;

val addry_close_precondition_def = Define `
  addry_close_precondition
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
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
      (sx : word32)
      (y1 : 'p)
      (x1 : 'p)
      (nr1 : 'p)
      (ny1 : 'p)
      (nx1 : 'p)
      (m : 'm) <=>
    writable y1 = T /\
    writable nr1 = T /\
    ok m = T /\
    (0 : int) <= w2i sx /\
    w2i sx <= w2i sx /\
    addry_identical
      data_length pelts offset minimum maximum zone nr1 ny1 /\
    addry_nonoverlap offset ny1 nx1 (w2i sx) /\
    zx m = zone y1 /\
    zy m = zone x1 /\
    lx m = sx /\
    ly m = sx`;

val addry_same_alias_memory_def = Define `
  addry_same_alias_memory
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

val addry_close_intermediate_def = Define `
  addry_close_intermediate
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (mx : 'm -> word32)
      (my : 'm -> word32)
      (sx : word32)
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
    addry_map_eq_sub_shift
      pelts ny1 y2 (offset ny2) (offset y2) (w2i sx) /\
    addry_map_eq_sub_shift
      pelts nx1 x2 (offset nx2) (offset x2) (w2i sx) /\
    (!j : int.
       j < offset y2 \/ offset y2 + w2i sx <= j ==>
       pelts y2 j = pelts y1 j) /\
    (!j : int.
       j < offset x2 \/ offset x2 + w2i sx <= j ==>
       pelts x2 j = pelts x1 j) /\
    addry_plength data_length y2 = addry_plength data_length y1 /\
    addry_plength data_length x2 = addry_plength data_length x1 /\
    minimum y2 = minimum y1 /\
    minimum x2 = minimum x1`;

val addry_final_postcondition_def = Define `
  addry_final_postcondition
      (data_length : 'p -> num)
      (pelts : 'p -> int -> word64)
      (offset : 'p -> int)
      (minimum : 'p -> int)
      (maximum : 'p -> int)
      (sy : word32)
      (sx : word32)
      (x : 'p)
      (y : 'p)
      (x2 : 'p)
      (y2 : 'p)
      (res : word64) <=>
    addry_value pelts offset y2 (w2i sx) +
        addry_radix_power (w2i sx) * &(w2n res) =
      addry_value pelts offset x (w2i sx) +
        addry_value pelts offset y (w2i sy) /\
    ((0 : int) <= &(w2n res) /\ &(w2n res) <= (1 : int)) /\
    (!j : int.
       j < offset y2 \/ offset y2 + w2i sx <= j ==>
       pelts y2 j = pelts y j) /\
    (!j : int.
       pelts x2 j = pelts x j) /\
    addry_value pelts offset x2 (w2i sx) =
      addry_value pelts offset x (w2i sx) /\
    minimum x2 = minimum x /\
    maximum x2 = maximum x /\
    addry_plength data_length x2 = addry_plength data_length x /\
    minimum y2 = minimum y /\
    maximum y2 = maximum y /\
    addry_plength data_length y2 = addry_plength data_length y`;

val add_Add_add_ry_vc =
  ``!data_length : 'p -> num.
    !pelts : 'p -> int -> word64.
    !offset minimum maximum : 'p -> int.
    !writable : 'p -> bool.
    !zone : 'p -> 'z.
    !zr zx zy : 'm -> 'z.
    !mr mx my lr lx ly : 'm -> word32.
    !ok : 'm -> bool.
    !sy sx : word32.
    !x y : 'p.
      (0 : int) <= w2i sy ==>
      w2i sy <= w2i sx ==>
      addry_valid data_length offset minimum maximum x (w2i sx) ==>
      addry_valid data_length offset minimum maximum y (w2i sx) ==>
      writable y = T ==>
      addry_valid data_length offset minimum maximum y (w2i sx) /\
      addry_valid data_length offset minimum maximum x (w2i sx) /\
      (0 : int) <= w2i sx /\
      w2i sx <= w2i sx /\
      writable y = T /\
      (!y1 x1 : 'p.
         addry_same_offset_writable_zone
           offset writable zone y1 y ==>
         addry_same_offset_writable_zone
           offset writable zone x1 x ==>
         (!nr ny nx : 'p.
          !m : 'm.
            addry_open_precondition
              data_length pelts offset minimum maximum writable zone
              zx zy mx my lx ly ok sx x y y1 x1 nr ny nx m ==>
            addry_call_precondition
              data_length pelts offset minimum maximum writable
              sy sx nr ny nx /\
            (!nx1 ny1 nr1 : 'p.
               addry_rebased_snapshot
                 data_length pelts offset minimum maximum writable zone
                 nx1 nr1 nx ==>
               addry_rebased_snapshot
                 data_length pelts offset minimum maximum writable zone
                 ny1 nr1 ny ==>
               addry_snapshot_metadata
                 data_length offset minimum maximum writable zone nr1 nr ==>
               (!res : word64.
                  addry_wmpn_postcondition
                    pelts offset sy sx nr ny nx nr1 ny1 nx1 res ==>
                  addry_close_precondition
                    data_length pelts offset minimum maximum writable zone
                    zx zy lx ly ok sx y1 x1 nr1 ny1 nx1 m /\
                  (!m1 : 'm.
                   !nx2 ny2 y2 x2 : 'p.
                     addry_same_alias_memory
                       zr zx zy mr mx my lr lx ly m1 m ==>
                     addry_same_offset_writable_zone
                       offset writable zone nx2 nx1 ==>
                     addry_same_offset_writable_zone
                       offset writable zone ny2 ny1 ==>
                     addry_same_offset_minimum_writable_zone
                       offset minimum writable zone y2 y1 ==>
                     addry_same_offset_minimum_writable_zone
                       offset minimum writable zone x2 x1 ==>
                     addry_close_intermediate
                       data_length pelts offset minimum maximum mx my sx m1
                       nx1 ny1 nx2 ny2 y1 x1 y2 x2 ==>
                     addry_final_postcondition
                       data_length pelts offset minimum maximum
                       sy sx x y x2 y2 res)))))``;
