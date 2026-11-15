(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_redcifyqtvc: the verification condition for
  copying a multiprecision integer into zero-extended scratch storage and
  obtaining its radix-scaled Euclidean remainder by division.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory wordsTheory;

val _ = type_abbrev
  ("powm_redcify_ptr",
   ``:(int -> word64) #
      (int # (int # (int # (int # (bool # 'z)))))``);

val powm_redcify_radix_def = Define `
  powm_redcify_radix = (18446744073709551616 : int)`;

val powm_redcify_to_num_def = Define `
  powm_redcify_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val powm_redcify_u64_def = Define `
  powm_redcify_u64 (x : word64) = &(w2n x)`;

val powm_redcify_u32_def = Define `
  powm_redcify_u32 (x : word32) = &(w2n x)`;

val powm_redcify_i32_def = Define `
  powm_redcify_i32 (x : word32) = w2i x`;

val powm_redcify_int32_in_bounds_def = Define `
  powm_redcify_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val powm_redcify_ipow_def = Define `
  powm_redcify_ipow (base : int) (exponent : int) =
    base ** powm_redcify_to_num exponent`;

val powm_redcify_data_def = Define `
  powm_redcify_data (p : 'z powm_redcify_ptr) = FST p`;

val powm_redcify_plength_def = Define `
  powm_redcify_plength (p : 'z powm_redcify_ptr) =
    FST (SND p)`;

val powm_redcify_offset_def = Define `
  powm_redcify_offset (p : 'z powm_redcify_ptr) =
    FST (SND (SND p))`;

val powm_redcify_minimum_def = Define `
  powm_redcify_minimum (p : 'z powm_redcify_ptr) =
    FST (SND (SND (SND p)))`;

val powm_redcify_maximum_def = Define `
  powm_redcify_maximum (p : 'z powm_redcify_ptr) =
    FST (SND (SND (SND (SND p))))`;

val powm_redcify_writable_def = Define `
  powm_redcify_writable (p : 'z powm_redcify_ptr) =
    FST (SND (SND (SND (SND (SND p)))))`;

val powm_redcify_zone_def = Define `
  powm_redcify_zone (p : 'z powm_redcify_ptr) =
    SND (SND (SND (SND (SND (SND p)))))`;

val powm_redcify_pelts_def = Define `
  powm_redcify_pelts (p : 'z powm_redcify_ptr) (index : int) =
    powm_redcify_data p index`;

val powm_redcify_valid_def = Define `
  powm_redcify_valid (p : 'z powm_redcify_ptr) (size : int) <=>
    powm_redcify_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= powm_redcify_minimum p /\
     powm_redcify_minimum p <= powm_redcify_offset p) /\
    powm_redcify_offset p + size <= powm_redcify_maximum p /\
    powm_redcify_maximum p <= powm_redcify_plength p`;

val powm_redcify_value_from_def = Define `
  (powm_redcify_value_from
      (m : int -> word64) (index : int) 0 = (0 : int)) /\
  (powm_redcify_value_from m index (SUC count) =
     powm_redcify_u64 (m index) +
       powm_redcify_radix *
         powm_redcify_value_from m (index + (1 : int)) count)`;

val powm_redcify_value_def = Define `
  powm_redcify_value (p : 'z powm_redcify_ptr) (size : int) =
    powm_redcify_value_from
      (powm_redcify_pelts p)
      (powm_redcify_offset p)
      (powm_redcify_to_num size)`;

val powm_redcify_redc_def = Define `
  powm_redcify_redc (ur : int) (u : int) (n : int) (m : int) <=>
    ur % m =
      (powm_redcify_ipow powm_redcify_radix n * u) % m`;

val powm_redcify_allocated_def = Define `
  powm_redcify_allocated
      (p : 'z powm_redcify_ptr) (size : int) <=>
    powm_redcify_plength p = size /\
    powm_redcify_offset p = (0 : int) /\
    powm_redcify_minimum p = (0 : int) /\
    powm_redcify_maximum p = size /\
    powm_redcify_writable p = T`;

val powm_redcify_same_shape_def = Define `
  powm_redcify_same_shape
      (newer : 'z powm_redcify_ptr)
      (older : 'z powm_redcify_ptr) <=>
    powm_redcify_plength newer = powm_redcify_plength older /\
    powm_redcify_offset newer = powm_redcify_offset older /\
    powm_redcify_minimum newer = powm_redcify_minimum older /\
    powm_redcify_maximum newer = powm_redcify_maximum older /\
    powm_redcify_writable newer = powm_redcify_writable older /\
    powm_redcify_zone newer = powm_redcify_zone older`;

val powm_redcify_outside_unchanged_def = Define `
  powm_redcify_outside_unchanged
      (current : 'z powm_redcify_ptr)
      (original : 'z powm_redcify_ptr)
      (size : int) <=>
    !j : int.
      j < powm_redcify_offset current \/
      powm_redcify_offset current + size <= j
      ==>
      powm_redcify_pelts current j =
        powm_redcify_pelts original j`;

val powm_redcify_shifted_def = Define `
  powm_redcify_shifted
      (shifted : 'z powm_redcify_ptr)
      (base : 'z powm_redcify_ptr)
      (displacement : int) <=>
    powm_redcify_offset shifted =
      powm_redcify_offset base + displacement /\
    powm_redcify_plength shifted = powm_redcify_plength base /\
    powm_redcify_pelts shifted = powm_redcify_pelts base /\
    powm_redcify_data shifted = powm_redcify_data base /\
    powm_redcify_minimum shifted = powm_redcify_minimum base /\
    powm_redcify_maximum shifted = powm_redcify_maximum base /\
    powm_redcify_zone shifted = powm_redcify_zone base /\
    powm_redcify_writable shifted = powm_redcify_writable base`;

val powm_redcify_copy_bridge_def = Define `
  powm_redcify_copy_bridge
      (copy_view : 'z powm_redcify_ptr)
      (updated_base : 'z powm_redcify_ptr)
      (shifted_base : 'z powm_redcify_ptr) <=>
    powm_redcify_data copy_view =
      powm_redcify_data updated_base /\
    powm_redcify_plength updated_base =
      powm_redcify_plength shifted_base /\
    powm_redcify_offset copy_view =
      powm_redcify_offset shifted_base /\
    powm_redcify_minimum copy_view =
      powm_redcify_minimum shifted_base /\
    powm_redcify_maximum copy_view =
      powm_redcify_maximum shifted_base /\
    powm_redcify_writable copy_view =
      powm_redcify_writable shifted_base /\
    powm_redcify_zone copy_view =
      powm_redcify_zone shifted_base`;

val powm_redcify_map_eq_sub_shift_def = Define `
  powm_redcify_map_eq_sub_shift
      (first : 'z powm_redcify_ptr)
      (second : 'z powm_redcify_ptr)
      (first_offset : int)
      (second_offset : int)
      (size : int) <=>
    !i : int.
      (0 : int) <= i /\ i < size
      ==>
      powm_redcify_pelts first (first_offset + i) =
        powm_redcify_pelts second (second_offset + i)`;

val powm_redcify_final_stage_def = Define `
  powm_redcify_final_stage
      (tp2 : 'z powm_redcify_ptr)
      (qp : 'z powm_redcify_ptr)
      (mp : 'z powm_redcify_ptr)
      (rp : 'z powm_redcify_ptr)
      (up : 'z powm_redcify_ptr)
      (o7 : word32)
      (n : word32)
      (un : word32) <=>
    (((1 : int) <= powm_redcify_i32 n /\
      powm_redcify_i32 n <= powm_redcify_i32 o7 /\
      powm_redcify_i32 o7 <= (2147483647 : int) - (1 : int)) /\
     powm_redcify_valid tp2 (powm_redcify_i32 o7) /\
     powm_redcify_valid mp (powm_redcify_i32 n) /\
     powm_redcify_valid qp
       (powm_redcify_i32 o7 - powm_redcify_i32 n + (1 : int)) /\
     powm_redcify_valid rp (powm_redcify_i32 n) /\
     (powm_redcify_writable qp = T /\
      powm_redcify_writable rp = T) /\
     (0 : int) <
       powm_redcify_u64
         (powm_redcify_pelts mp
           (powm_redcify_offset mp +
            powm_redcify_i32 n - (1 : int)))) /\
    (!qp1 rp1 : 'z powm_redcify_ptr.
       powm_redcify_same_shape qp1 qp
       ==>
       powm_redcify_same_shape rp1 rp
       ==>
       powm_redcify_value tp2 (powm_redcify_i32 o7) =
           powm_redcify_value qp1
             (powm_redcify_i32 o7 -
              powm_redcify_i32 n + (1 : int)) *
             powm_redcify_value mp (powm_redcify_i32 n) +
           powm_redcify_value rp1 (powm_redcify_i32 n) /\
       powm_redcify_value rp1 (powm_redcify_i32 n) <
         powm_redcify_value mp (powm_redcify_i32 n)
       ==>
       powm_redcify_value rp1 (powm_redcify_i32 n) =
           (powm_redcify_ipow
              powm_redcify_radix (powm_redcify_i32 n) *
            powm_redcify_value up (powm_redcify_i32 un)) %
             powm_redcify_value mp (powm_redcify_i32 n) /\
       powm_redcify_redc
         (powm_redcify_value rp1 (powm_redcify_i32 n))
         (powm_redcify_value up (powm_redcify_i32 un))
         (powm_redcify_i32 n)
         (powm_redcify_value mp (powm_redcify_i32 n)))`;

val powm_Powm_redcifyqtvc_statement =
  ``!rp : 'z powm_redcify_ptr.
    !n : word32.
    !up : 'z powm_redcify_ptr.
    !un : word32.
    !mp : 'z powm_redcify_ptr.
      powm_redcify_valid rp (powm_redcify_i32 n)
      ==>
      powm_redcify_valid up (powm_redcify_i32 un)
      ==>
      powm_redcify_valid mp (powm_redcify_i32 n)
      ==>
      (1 : int) <= powm_redcify_i32 n
      ==>
      (1 : int) <= powm_redcify_i32 un
      ==>
      powm_redcify_i32 un + powm_redcify_i32 n <
        (2147483647 : int)
      ==>
      (0 : int) <
        powm_redcify_u64
          (powm_redcify_pelts mp
            (powm_redcify_offset mp +
             powm_redcify_i32 n - (1 : int)))
      ==>
      powm_redcify_writable rp = T
      ==>
      powm_redcify_int32_in_bounds
        (powm_redcify_i32 un + powm_redcify_i32 n) /\
      (!o1 : word32.
         powm_redcify_i32 o1 =
           powm_redcify_i32 un + powm_redcify_i32 n
         ==>
         (0 : int) <= powm_redcify_i32 o1 /\
         (!o2 : word32.
            powm_redcify_u32 o2 = powm_redcify_i32 o1
            ==>
            (0 : int) <= powm_redcify_u32 o2 /\
            (!tp : 'z powm_redcify_ptr.
               powm_redcify_allocated tp (powm_redcify_u32 o2)
               ==>
               powm_redcify_int32_in_bounds
                 (powm_redcify_i32 un + (1 : int)) /\
               (!o3 : word32.
                  powm_redcify_i32 o3 =
                    powm_redcify_i32 un + (1 : int)
                  ==>
                  (0 : int) <= powm_redcify_i32 o3 /\
                  (!o4 : word32.
                     powm_redcify_u32 o4 = powm_redcify_i32 o3
                     ==>
                     (0 : int) <= powm_redcify_u32 o4 /\
                     (!qp : 'z powm_redcify_ptr.
                        powm_redcify_allocated qp
                          (powm_redcify_u32 o4)
                        ==>
                        (powm_redcify_valid tp
                           (powm_redcify_i32 n) /\
                         powm_redcify_writable tp = T) /\
                        (!tp1 : 'z powm_redcify_ptr.
                           powm_redcify_same_shape tp1 tp
                           ==>
                           powm_redcify_value tp1
                               (powm_redcify_i32 n) =
                             (0 : int) /\
                           powm_redcify_outside_unchanged
                             tp1 tp (powm_redcify_i32 n)
                           ==>
                           (powm_redcify_minimum tp1 <=
                              powm_redcify_offset tp1 +
                                powm_redcify_i32 n /\
                            powm_redcify_offset tp1 +
                                powm_redcify_i32 n <=
                              powm_redcify_maximum tp1) /\
                           (!o5 : 'z powm_redcify_ptr.
                              powm_redcify_shifted
                                o5 tp1 (powm_redcify_i32 n)
                              ==>
                              (powm_redcify_valid up
                                 (powm_redcify_i32 un) /\
                               powm_redcify_valid o5
                                 (powm_redcify_i32 un) /\
                               powm_redcify_writable o5 = T) /\
                              (!o6 tp2 : 'z powm_redcify_ptr.
                                 powm_redcify_copy_bridge o6 tp2 o5
                                 ==>
                                 powm_redcify_same_shape tp2 tp1
                                 ==>
                                 powm_redcify_map_eq_sub_shift
                                     o6 up
                                     (powm_redcify_offset o6)
                                     (powm_redcify_offset up)
                                     (powm_redcify_i32 un) /\
                                   powm_redcify_outside_unchanged
                                     o6 o5 (powm_redcify_i32 un)
                                 ==>
                                 powm_redcify_int32_in_bounds
                                   (powm_redcify_i32 un +
                                    powm_redcify_i32 n) /\
                                 (!o7 : word32.
                                    powm_redcify_i32 o7 =
                                      powm_redcify_i32 un +
                                        powm_redcify_i32 n
                                    ==>
                                    powm_redcify_final_stage
                                      tp2 qp mp rp up o7 n un))))))))))``;
