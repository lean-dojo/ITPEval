(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_getbitqtvc: the verification condition for
  extracting one bit from a valid multiprecision limb array and relating it
  to both full-array division and the prefix-value recurrence.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val _ = type_abbrev
  ("powm_getbit_ptr",
   ``:word64 list # (int # (int # (int # (bool # 'z))))``);

val powm_getbit_radix_def = Define `
  powm_getbit_radix = (18446744073709551616 : int)`;

val powm_getbit_to_num_def = Define `
  powm_getbit_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val powm_getbit_u64_def = Define `
  powm_getbit_u64 (x : word64) = &(w2n x)`;

val powm_getbit_i32_def = Define `
  powm_getbit_i32 (x : word32) = w2i x`;

val powm_getbit_int32_in_bounds_def = Define `
  powm_getbit_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val powm_getbit_uint64_in_bounds_def = Define `
  powm_getbit_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val powm_getbit_ipow_def = Define `
  powm_getbit_ipow (base : int) (exponent : int) =
    base ** powm_getbit_to_num exponent`;

val powm_getbit_ediv_def = Define `
  powm_getbit_ediv (x : int) (y : int) = x / y`;

val powm_getbit_cdiv_def = Define `
  powm_getbit_cdiv (x : int) (y : int) = x quot y`;

val powm_getbit_cmod_def = Define `
  powm_getbit_cmod (x : int) (y : int) = x rem y`;

val powm_getbit_data_def = Define `
  powm_getbit_data (p : 'z powm_getbit_ptr) = FST p`;

val powm_getbit_offset_def = Define `
  powm_getbit_offset (p : 'z powm_getbit_ptr) = FST (SND p)`;

val powm_getbit_minimum_def = Define `
  powm_getbit_minimum (p : 'z powm_getbit_ptr) =
    FST (SND (SND p))`;

val powm_getbit_maximum_def = Define `
  powm_getbit_maximum (p : 'z powm_getbit_ptr) =
    FST (SND (SND (SND p)))`;

val powm_getbit_writable_def = Define `
  powm_getbit_writable (p : 'z powm_getbit_ptr) =
    FST (SND (SND (SND (SND p))))`;

val powm_getbit_zone_def = Define `
  powm_getbit_zone (p : 'z powm_getbit_ptr) =
    SND (SND (SND (SND (SND p))))`;

val powm_getbit_plength_def = Define `
  powm_getbit_plength (p : 'z powm_getbit_ptr) =
    &(LENGTH (powm_getbit_data p))`;

val powm_getbit_pelts_def = Define `
  powm_getbit_pelts (p : 'z powm_getbit_ptr) (index : int) =
    if powm_getbit_to_num index < LENGTH (powm_getbit_data p) then
      EL (powm_getbit_to_num index) (powm_getbit_data p)
    else
      (0w : word64)`;

val powm_getbit_valid_def = Define `
  powm_getbit_valid (p : 'z powm_getbit_ptr) (size : int) <=>
    powm_getbit_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= powm_getbit_minimum p /\
     powm_getbit_minimum p <= powm_getbit_offset p) /\
    powm_getbit_offset p + size <= powm_getbit_maximum p /\
    powm_getbit_maximum p <= powm_getbit_plength p`;

val powm_getbit_value_from_def = Define `
  (powm_getbit_value_from
      (m : int -> word64) (index : int) 0 = (0 : int)) /\
  (powm_getbit_value_from m index (SUC count) =
     powm_getbit_u64 (m index) +
       powm_getbit_radix *
         powm_getbit_value_from m (index + (1 : int)) count)`;

val powm_getbit_value_def = Define `
  powm_getbit_value (p : 'z powm_getbit_ptr) (size : int) =
    powm_getbit_value_from
      (powm_getbit_pelts p)
      (powm_getbit_offset p)
      (powm_getbit_to_num size)`;

val powm_getbit_valueb_def = Define `
  powm_getbit_valueb (p : 'z powm_getbit_ptr) (nbits : int) =
    if nbits < (0 : int) then
      (0 : int)
    else
      let i = powm_getbit_ediv nbits (64 : int) in
        powm_getbit_value p i +
        powm_getbit_ipow powm_getbit_radix i *
          (powm_getbit_u64
             (powm_getbit_pelts
                p (powm_getbit_offset p + i)) %
           powm_getbit_ipow
             (2 : int) (nbits - (64 : int) * i))`;

val powm_Powm_getbitqtvc_statement =
  ``!p : 'z powm_getbit_ptr.
    !pn bi : word32.
      powm_getbit_valid p (powm_getbit_i32 pn)
      ==>
      (1 : int) <= powm_getbit_i32 bi
      ==>
      powm_getbit_ediv
          (powm_getbit_i32 bi + (63 : int)) (64 : int) <=
        powm_getbit_i32 pn
      ==>
      powm_getbit_int32_in_bounds
        (powm_getbit_i32 bi - (1 : int)) /\
      (!o1 : word32.
         powm_getbit_i32 o1 =
           powm_getbit_i32 bi - (1 : int)
         ==>
         (~((64 : int) = (0 : int)) /\
          powm_getbit_int32_in_bounds
            (powm_getbit_cdiv
               (powm_getbit_i32 o1) (64 : int))) /\
         (!i : word32.
            powm_getbit_i32 i =
              powm_getbit_cdiv
                (powm_getbit_i32 o1) (64 : int)
            ==>
            powm_getbit_int32_in_bounds
              (powm_getbit_i32 bi - (1 : int)) /\
            (!o2 : word32.
               powm_getbit_i32 o2 =
                 powm_getbit_i32 bi - (1 : int)
               ==>
               (0 : int) <= powm_getbit_i32 o2 /\
               (!o3 : word64.
                  powm_getbit_u64 o3 = powm_getbit_i32 o2
                  ==>
                  (~((64 : int) = (0 : int)) /\
                   powm_getbit_uint64_in_bounds
                     (powm_getbit_cmod
                        (powm_getbit_u64 o3) (64 : int))) /\
                  (!mi : word64.
                     powm_getbit_u64 mi =
                       powm_getbit_cmod
                         (powm_getbit_u64 o3) (64 : int)
                     ==>
                     (powm_getbit_minimum p <=
                        powm_getbit_offset p +
                          powm_getbit_i32 i /\
                      powm_getbit_offset p +
                          powm_getbit_i32 i <
                        powm_getbit_maximum p) /\
                     powm_getbit_int32_in_bounds
                       (powm_getbit_i32 i + (1 : int)) /\
                     (!o4 : word32.
                        powm_getbit_i32 o4 =
                          powm_getbit_i32 i + (1 : int)
                        ==>
                        (powm_getbit_minimum p <=
                           powm_getbit_offset p +
                             powm_getbit_i32 o4 /\
                         powm_getbit_offset p +
                             powm_getbit_i32 o4 <=
                           powm_getbit_maximum p) /\
                        (!p' : 'z powm_getbit_ptr.
                           powm_getbit_offset p' =
                             powm_getbit_offset p +
                               powm_getbit_i32 o4 /\
                           powm_getbit_plength p' =
                             powm_getbit_plength p /\
                           powm_getbit_pelts p' =
                             powm_getbit_pelts p /\
                           powm_getbit_data p' =
                             powm_getbit_data p /\
                           powm_getbit_minimum p' =
                             powm_getbit_minimum p /\
                           powm_getbit_maximum p' =
                             powm_getbit_maximum p /\
                           powm_getbit_zone p' =
                             powm_getbit_zone p /\
                           powm_getbit_writable p' =
                             powm_getbit_writable p
                           ==>
                           ((0 : int) <= powm_getbit_u64 mi /\
                            powm_getbit_u64 mi < (64 : int)) /\
                           (!lps : word64.
                              powm_getbit_u64 lps =
                                powm_getbit_ediv
                                  (powm_getbit_u64
                                    (powm_getbit_pelts p
                                      (powm_getbit_offset p +
                                       powm_getbit_i32 i)))
                                  (powm_getbit_ipow
                                    (2 : int)
                                    (powm_getbit_u64 mi))
                              ==>
                              ~(powm_getbit_ipow
                                  (2 : int)
                                  (powm_getbit_u64 mi) =
                                (0 : int)) /\
                              (~((2 : int) = (0 : int)) /\
                               powm_getbit_uint64_in_bounds
                                 (powm_getbit_cmod
                                   (powm_getbit_u64 lps)
                                   (2 : int))) /\
                              (!res : word64.
                                 powm_getbit_u64 res =
                                   powm_getbit_cmod
                                     (powm_getbit_u64 lps)
                                     (2 : int)
                                 ==>
                                 ~((2 : int) = (0 : int)) /\
                                 (~((2 : int) = (0 : int)) /\
                                  powm_getbit_uint64_in_bounds
                                    (powm_getbit_cmod
                                      (powm_getbit_u64 lps)
                                      (2 : int))) /\
                                 (!result : word64.
                                    powm_getbit_u64 result =
                                      powm_getbit_cmod
                                        (powm_getbit_u64 lps)
                                        (2 : int)
                                    ==>
                                    ((0 : int) <=
                                       powm_getbit_u64 result /\
                                     powm_getbit_u64 result <=
                                       (1 : int)) /\
                                    powm_getbit_u64 result =
                                      powm_getbit_ediv
                                        (powm_getbit_value p
                                          (powm_getbit_i32 pn))
                                        (powm_getbit_ipow
                                          (2 : int)
                                          (powm_getbit_i32 bi -
                                           (1 : int))) %
                                        (2 : int) /\
                                    powm_getbit_valueb p
                                        (powm_getbit_i32 bi) =
                                      powm_getbit_valueb p
                                          (powm_getbit_i32 bi -
                                           (1 : int)) +
                                      powm_getbit_ipow
                                          (2 : int)
                                          (powm_getbit_i32 bi -
                                           (1 : int)) *
                                        powm_getbit_u64
                                          result))))))))))``;
