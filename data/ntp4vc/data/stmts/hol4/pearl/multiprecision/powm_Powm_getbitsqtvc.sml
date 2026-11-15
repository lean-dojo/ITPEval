(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_getbitsqtvc: the verification condition for
  extracting a nonempty bit window from a multiprecision integer, including
  the one-limb and two-limb cases and the resulting prefix-value equations.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val _ = type_abbrev
  ("gbitsq_ptr",
   ``:word64 list # (int # (int # (int # (bool # 'z))))``);

val gbitsq_radix_def = Define `
  gbitsq_radix = (18446744073709551616 : int)`;

val gbitsq_to_num_def = Define `
  gbitsq_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val gbitsq_u64_def = Define `
  gbitsq_u64 (x : word64) = &(w2n x)`;

val gbitsq_i32_def = Define `
  gbitsq_i32 (x : word32) = w2i x`;

val gbitsq_int32_in_bounds_def = Define `
  gbitsq_int32_in_bounds (z : int) <=>
    -(2147483648 : int) <= z /\ z <= (2147483647 : int)`;

val gbitsq_uint64_in_bounds_def = Define `
  gbitsq_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val gbitsq_ipow_def = Define `
  gbitsq_ipow (base : int) (exponent : int) =
    base ** gbitsq_to_num exponent`;

val gbitsq_ediv_def = Define `
  gbitsq_ediv (x : int) (y : int) = x / y`;

val gbitsq_cdiv_def = Define `
  gbitsq_cdiv (x : int) (y : int) = x quot y`;

val gbitsq_cmod_def = Define `
  gbitsq_cmod (x : int) (y : int) = x rem y`;

val gbitsq_data_def = Define `
  gbitsq_data (p : 'z gbitsq_ptr) = FST p`;

val gbitsq_offset_def = Define `
  gbitsq_offset (p : 'z gbitsq_ptr) = FST (SND p)`;

val gbitsq_minimum_def = Define `
  gbitsq_minimum (p : 'z gbitsq_ptr) =
    FST (SND (SND p))`;

val gbitsq_maximum_def = Define `
  gbitsq_maximum (p : 'z gbitsq_ptr) =
    FST (SND (SND (SND p)))`;

val gbitsq_writable_def = Define `
  gbitsq_writable (p : 'z gbitsq_ptr) =
    FST (SND (SND (SND (SND p))))`;

val gbitsq_zone_def = Define `
  gbitsq_zone (p : 'z gbitsq_ptr) =
    SND (SND (SND (SND (SND p))))`;

val gbitsq_plength_def = Define `
  gbitsq_plength (p : 'z gbitsq_ptr) =
    &(LENGTH (gbitsq_data p))`;

val gbitsq_pelts_def = Define `
  gbitsq_pelts (p : 'z gbitsq_ptr) (index : int) =
    if gbitsq_to_num index < LENGTH (gbitsq_data p) then
      EL (gbitsq_to_num index) (gbitsq_data p)
    else
      (0w : word64)`;

val gbitsq_valid_def = Define `
  gbitsq_valid (p : 'z gbitsq_ptr) (size : int) <=>
    gbitsq_int32_in_bounds size /\
    (0 : int) <= size /\
    ((0 : int) <= gbitsq_minimum p /\
     gbitsq_minimum p <= gbitsq_offset p) /\
    gbitsq_offset p + size <= gbitsq_maximum p /\
    gbitsq_maximum p <= gbitsq_plength p`;

val gbitsq_value_from_def = Define `
  (gbitsq_value_from
      (m : int -> word64) (index : int) 0 = (0 : int)) /\
  (gbitsq_value_from m index (SUC count) =
     gbitsq_u64 (m index) +
       gbitsq_radix *
         gbitsq_value_from m (index + (1 : int)) count)`;

val gbitsq_value_def = Define `
  gbitsq_value (p : 'z gbitsq_ptr) (size : int) =
    gbitsq_value_from
      (gbitsq_pelts p)
      (gbitsq_offset p)
      (gbitsq_to_num size)`;

val gbitsq_valueb_def = Define `
  gbitsq_valueb (p : 'z gbitsq_ptr) (nbits : int) =
    if nbits < (0 : int) then
      (0 : int)
    else
      let i = gbitsq_ediv nbits (64 : int) in
        gbitsq_value p i +
        gbitsq_ipow gbitsq_radix i *
          gbitsq_cmod
            (gbitsq_u64
              (gbitsq_pelts p (gbitsq_offset p + i)))
            (gbitsq_ipow
              (2 : int) (nbits - (64 : int) * i))`;

val gbitsq_shifted_pointer_def = Define `
  gbitsq_shifted_pointer
      (shifted : 'z gbitsq_ptr)
      (base : 'z gbitsq_ptr)
      (displacement : int) <=>
    gbitsq_offset shifted = gbitsq_offset base + displacement /\
    gbitsq_plength shifted = gbitsq_plength base /\
    gbitsq_pelts shifted = gbitsq_pelts base /\
    gbitsq_data shifted = gbitsq_data base /\
    gbitsq_minimum shifted = gbitsq_minimum base /\
    gbitsq_maximum shifted = gbitsq_maximum base /\
    gbitsq_zone shifted = gbitsq_zone base /\
    gbitsq_writable shifted = gbitsq_writable base`;

val gbitsq_result_postcondition_def = Define `
  gbitsq_result_postcondition
      (p : 'z gbitsq_ptr)
      (pn : word32)
      (bi : word32)
      (nbits : word32)
      (result : word64) <=>
    (gbitsq_i32 nbits <= gbitsq_i32 bi
     ==>
     gbitsq_valueb p (gbitsq_i32 bi) =
       gbitsq_valueb p
         (gbitsq_i32 bi - gbitsq_i32 nbits) +
       gbitsq_ipow
         (2 : int) (gbitsq_i32 bi - gbitsq_i32 nbits) *
       gbitsq_u64 result) /\
    (gbitsq_i32 bi < gbitsq_i32 nbits
     ==>
     gbitsq_valueb p (gbitsq_i32 bi) = gbitsq_u64 result) /\
    ((0 : int) <= gbitsq_u64 result /\
     gbitsq_u64 result <
       gbitsq_ipow (2 : int) (gbitsq_i32 nbits)) /\
    (gbitsq_i32 nbits <= gbitsq_i32 bi
     ==>
     gbitsq_u64 result =
       gbitsq_cmod
         (gbitsq_ediv
           (gbitsq_value p (gbitsq_i32 pn))
           (gbitsq_ipow
             (2 : int) (gbitsq_i32 bi - gbitsq_i32 nbits)))
         (gbitsq_ipow (2 : int) (gbitsq_i32 nbits)))`;

val gbitsq_reduced_result_def = Define `
  gbitsq_reduced_result
      (p : 'z gbitsq_ptr)
      (pn : word32)
      (bi : word32)
      (nbits : word32)
      (dividend : int)
      (divisor : int) <=>
    ~(divisor = (0 : int)) /\
    gbitsq_uint64_in_bounds
      (gbitsq_cmod dividend divisor) /\
    (!result : word64.
       gbitsq_u64 result = gbitsq_cmod dividend divisor
       ==>
       gbitsq_result_postcondition p pn bi nbits result)`;

val gbitsq_small_branch_def = Define `
  gbitsq_small_branch
      (p : 'z gbitsq_ptr)
      (pn : word32)
      (bi : word32)
      (nbits : word32) <=>
    (0 : int) <= gbitsq_i32 bi /\
    (!o1 : word64.
       gbitsq_u64 o1 = gbitsq_i32 bi
       ==>
       (((0 : int) <= gbitsq_u64 o1 /\
         gbitsq_u64 o1 < (64 : int)) /\
        gbitsq_ipow (2 : int) (gbitsq_u64 o1) *
          gbitsq_u64 (1w : word64) <=
          (18446744073709551615 : int)) /\
       (!o2 : word64.
          gbitsq_u64 o2 =
            gbitsq_ipow (2 : int) (gbitsq_u64 o1) *
            gbitsq_u64 (1w : word64)
          ==>
          (gbitsq_minimum p <= gbitsq_offset p /\
           gbitsq_offset p < gbitsq_maximum p) /\
          gbitsq_reduced_result p pn bi nbits
            (gbitsq_u64
              (gbitsq_pelts p (gbitsq_offset p)))
            (gbitsq_u64 o2)))`;

val gbitsq_one_limb_branch_def = Define `
  gbitsq_one_limb_branch
      (p : 'z gbitsq_ptr)
      (pn : word32)
      (bi : word32)
      (nbits : word32)
      (shifted : word64) <=>
    (0 : int) <= gbitsq_i32 nbits /\
    (!o7 : word64.
       gbitsq_u64 o7 = gbitsq_i32 nbits
       ==>
       (((0 : int) <= gbitsq_u64 o7 /\
         gbitsq_u64 o7 < (64 : int)) /\
        gbitsq_ipow (2 : int) (gbitsq_u64 o7) *
          gbitsq_u64 (1w : word64) <=
          (18446744073709551615 : int)) /\
       (!o8 : word64.
          gbitsq_u64 o8 =
            gbitsq_ipow (2 : int) (gbitsq_u64 o7) *
            gbitsq_u64 (1w : word64)
          ==>
          gbitsq_reduced_result p pn bi nbits
            (gbitsq_u64 shifted) (gbitsq_u64 o8)))`;

val gbitsq_two_limb_branch_def = Define `
  gbitsq_two_limb_branch
      (p : 'z gbitsq_ptr)
      (pn : word32)
      (bi : word32)
      (nbits : word32)
      (quotient : word32)
      (shifted : word64)
      (remaining : word32) <=>
    gbitsq_int32_in_bounds (gbitsq_i32 quotient + (1 : int)) /\
    (!o7 : word32.
       gbitsq_i32 o7 = gbitsq_i32 quotient + (1 : int)
       ==>
       (gbitsq_minimum p <=
          gbitsq_offset p + gbitsq_i32 o7 /\
        gbitsq_offset p + gbitsq_i32 o7 <
          gbitsq_maximum p) /\
       (0 : int) <= gbitsq_i32 remaining /\
       (!o8 : word64.
          gbitsq_u64 o8 = gbitsq_i32 remaining
          ==>
          ((0 : int) <= gbitsq_u64 o8 /\
           gbitsq_u64 o8 < (64 : int)) /\
          (!prs : word64.
             gbitsq_u64 prs =
               gbitsq_cmod
                 (gbitsq_u64
                    (gbitsq_pelts p
                      (gbitsq_offset p + gbitsq_i32 o7)) *
                  gbitsq_ipow (2 : int) (gbitsq_u64 o8))
                 gbitsq_radix /\
             gbitsq_u64 prs <=
               gbitsq_radix -
               gbitsq_ipow (2 : int) (gbitsq_u64 o8)
             ==>
             gbitsq_int32_in_bounds
               (gbitsq_i32 quotient + (2 : int)) /\
             (!o9 : word32.
                gbitsq_i32 o9 =
                  gbitsq_i32 quotient + (2 : int)
                ==>
                (gbitsq_minimum p <=
                   gbitsq_offset p + gbitsq_i32 o9 /\
                 gbitsq_offset p + gbitsq_i32 o9 <=
                   gbitsq_maximum p) /\
                (!p'' : 'z gbitsq_ptr.
                   gbitsq_shifted_pointer
                     p'' p (gbitsq_i32 o9)
                   ==>
                   ~(gbitsq_radix = (0 : int)) /\
                   gbitsq_uint64_in_bounds
                     (gbitsq_u64 shifted + gbitsq_u64 prs) /\
                   (!o10 : word64.
                      gbitsq_u64 o10 =
                        gbitsq_u64 shifted + gbitsq_u64 prs
                      ==>
                      (0 : int) <= gbitsq_i32 nbits /\
                      (!o11 : word64.
                         gbitsq_u64 o11 = gbitsq_i32 nbits
                         ==>
                         (((0 : int) <= gbitsq_u64 o11 /\
                           gbitsq_u64 o11 < (64 : int)) /\
                          gbitsq_ipow
                              (2 : int) (gbitsq_u64 o11) *
                            gbitsq_u64 (1w : word64) <=
                            (18446744073709551615 : int)) /\
                         (!o12 : word64.
                            gbitsq_u64 o12 =
                              gbitsq_ipow
                                  (2 : int) (gbitsq_u64 o11) *
                                gbitsq_u64 (1w : word64)
                            ==>
                            gbitsq_reduced_result
                              p pn bi nbits
                              (gbitsq_u64 o10)
                              (gbitsq_u64 o12)))))))))`;

val gbitsq_large_branch_def = Define `
  gbitsq_large_branch
      (p : 'z gbitsq_ptr)
      (pn : word32)
      (bi : word32)
      (nbits : word32) <=>
    gbitsq_int32_in_bounds
      (gbitsq_i32 bi - gbitsq_i32 nbits) /\
    (!difference : word32.
       gbitsq_i32 difference =
         gbitsq_i32 bi - gbitsq_i32 nbits
       ==>
       (~((64 : int) = (0 : int)) /\
        gbitsq_int32_in_bounds
          (gbitsq_cdiv (gbitsq_i32 difference) (64 : int))) /\
       (!quotient : word32.
          gbitsq_i32 quotient =
            gbitsq_cdiv (gbitsq_i32 difference) (64 : int)
          ==>
          (~((64 : int) = (0 : int)) /\
           gbitsq_int32_in_bounds
             (gbitsq_cmod
               (gbitsq_i32 difference) (64 : int))) /\
          (!remainder : word32.
             gbitsq_i32 remainder =
               gbitsq_cmod
                 (gbitsq_i32 difference) (64 : int)
             ==>
             (gbitsq_minimum p <=
                gbitsq_offset p + gbitsq_i32 quotient /\
              gbitsq_offset p + gbitsq_i32 quotient <
                gbitsq_maximum p) /\
             gbitsq_int32_in_bounds
               (gbitsq_i32 quotient + (1 : int)) /\
             (!o4 : word32.
                gbitsq_i32 o4 =
                  gbitsq_i32 quotient + (1 : int)
                ==>
                (gbitsq_minimum p <=
                   gbitsq_offset p + gbitsq_i32 o4 /\
                 gbitsq_offset p + gbitsq_i32 o4 <=
                   gbitsq_maximum p) /\
                (!p' : 'z gbitsq_ptr.
                   gbitsq_shifted_pointer
                     p' p (gbitsq_i32 o4)
                   ==>
                   (0 : int) <= gbitsq_i32 remainder /\
                   (!o5 : word64.
                      gbitsq_u64 o5 = gbitsq_i32 remainder
                      ==>
                      ((0 : int) <= gbitsq_u64 o5 /\
                       gbitsq_u64 o5 < (64 : int)) /\
                      (!shifted : word64.
                         gbitsq_u64 shifted =
                           gbitsq_ediv
                             (gbitsq_u64
                               (gbitsq_pelts p
                                 (gbitsq_offset p +
                                  gbitsq_i32 quotient)))
                             (gbitsq_ipow
                               (2 : int) (gbitsq_u64 o5))
                         ==>
                         ~(gbitsq_ipow
                             (2 : int) (gbitsq_i32 remainder) =
                           (0 : int)) /\
                         gbitsq_int32_in_bounds
                           ((64 : int) - gbitsq_i32 remainder) /\
                         (!remaining : word32.
                            gbitsq_i32 remaining =
                              (64 : int) - gbitsq_i32 remainder
                            ==>
                            if gbitsq_i32 remaining <
                               gbitsq_i32 nbits
                            then
                              gbitsq_two_limb_branch
                                p pn bi nbits quotient
                                shifted remaining
                            else
                              gbitsq_one_limb_branch
                                p pn bi nbits shifted))))))))`;

val powm_Powm_getbitsqtvc_statement =
  ``!nbits bi pn : word32.
    !p : 'z gbitsq_ptr.
      ((1 : int) <= gbitsq_i32 nbits /\
       gbitsq_i32 nbits < (64 : int) /\
       (0 : int) <= gbitsq_i32 bi /\
       (1 : int) <= gbitsq_i32 pn /\
       gbitsq_valid p (gbitsq_i32 pn) /\
       gbitsq_ediv
           (gbitsq_i32 bi + (63 : int)) (64 : int) <=
         gbitsq_i32 pn)
      ==>
      if gbitsq_i32 bi < gbitsq_i32 nbits
      then
        gbitsq_small_branch p pn bi nbits
      else
        gbitsq_large_branch p pn bi nbits``;
