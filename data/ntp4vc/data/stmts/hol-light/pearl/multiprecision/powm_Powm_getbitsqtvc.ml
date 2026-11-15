(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_getbitsqtvc: the verification condition for
  extracting a nonempty bit window from a multiprecision integer, including
  the one-limb and two-limb cases and the resulting prefix-value equations.
  This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("gbitsq_ptr",`:(int64 list)#(int#(int#(int#(bool#Z))))`);;

let gbitsq_radix = new_definition
  `gbitsq_radix = (&18446744073709551616:int)`;;

let gbitsq_u64 = new_definition
  `gbitsq_u64 (x:int64) = (&(val x):int)`;;

let gbitsq_int32_in_bounds = new_definition
  `gbitsq_int32_in_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let gbitsq_uint64_in_bounds = new_definition
  `gbitsq_uint64_in_bounds (x:int) <=>
     (&0:int) <= x /\ x <= (&18446744073709551615:int)`;;

let gbitsq_ipow = new_definition
  `gbitsq_ipow (base:int) (exponent:int) =
     base pow (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let gbitsq_data = new_definition
  `gbitsq_data (p:gbitsq_ptr) = FST p`;;

let gbitsq_offset = new_definition
  `gbitsq_offset (p:gbitsq_ptr) = FST (SND p)`;;

let gbitsq_minimum = new_definition
  `gbitsq_minimum (p:gbitsq_ptr) = FST (SND (SND p))`;;

let gbitsq_maximum = new_definition
  `gbitsq_maximum (p:gbitsq_ptr) = FST (SND (SND (SND p)))`;;

let gbitsq_writable = new_definition
  `gbitsq_writable (p:gbitsq_ptr) =
     FST (SND (SND (SND (SND p))))`;;

let gbitsq_zone = new_definition
  `gbitsq_zone (p:gbitsq_ptr) =
     SND (SND (SND (SND (SND p))))`;;

let gbitsq_pelts = new_definition
  `gbitsq_pelts p (i:int) =
     let k = if i < (&0:int) then 0 else num_of_int i in
     if k < LENGTH (gbitsq_data p)
     then EL k (gbitsq_data p)
     else (word 0:int64)`;;

let gbitsq_plength = new_definition
  `gbitsq_plength p = (&(LENGTH (gbitsq_data p)):int)`;;

let gbitsq_valid = new_definition
  `gbitsq_valid p (size:int) <=>
     gbitsq_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= gbitsq_minimum p /\
     gbitsq_minimum p <= gbitsq_offset p /\
     gbitsq_offset p + size <= gbitsq_maximum p /\
     gbitsq_maximum p <= gbitsq_plength p`;;

let gbitsq_value = new_definition
  `gbitsq_value p (size:int) =
     if size <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int size - 1)
         (\k. gbitsq_radix pow k *
              gbitsq_u64 (gbitsq_pelts p (gbitsq_offset p + &k)))`;;

let gbitsq_valueb = new_definition
  `gbitsq_valueb p (nbits:int) =
     if nbits < (&0:int) then (&0:int)
     else
       let i = nbits div (&64:int) in
       gbitsq_value p i +
       gbitsq_ipow gbitsq_radix i *
         (gbitsq_u64 (gbitsq_pelts p (gbitsq_offset p + i)) rem
          gbitsq_ipow (&2:int) (nbits - (&64:int) * i))`;;

let gbitsq_shifted_pointer = new_definition
  `gbitsq_shifted_pointer shifted base (displacement:int) <=>
     gbitsq_offset shifted = gbitsq_offset base + displacement /\
     gbitsq_plength shifted = gbitsq_plength base /\
     gbitsq_pelts shifted = gbitsq_pelts base /\
     gbitsq_data shifted = gbitsq_data base /\
     gbitsq_minimum shifted = gbitsq_minimum base /\
     gbitsq_maximum shifted = gbitsq_maximum base /\
     gbitsq_zone shifted = gbitsq_zone base /\
     gbitsq_writable shifted = gbitsq_writable base`;;

let gbitsq_result_postcondition = new_definition
  `gbitsq_result_postcondition
      (p:gbitsq_ptr) (pn:int32) (bi:int32) (nbits:int32)
      (result:int64) <=>
     (ival nbits <= ival bi
      ==> gbitsq_valueb p (ival bi) =
          gbitsq_valueb p (ival bi - ival nbits) +
          gbitsq_ipow (&2:int) (ival bi - ival nbits) *
          gbitsq_u64 result) /\
     (ival bi < ival nbits
      ==> gbitsq_valueb p (ival bi) = gbitsq_u64 result) /\
     ((&0:int) <= gbitsq_u64 result /\
      gbitsq_u64 result < gbitsq_ipow (&2:int) (ival nbits)) /\
     (ival nbits <= ival bi
      ==> gbitsq_u64 result =
          (gbitsq_value p (ival pn) div
           gbitsq_ipow (&2:int) (ival bi - ival nbits)) rem
          gbitsq_ipow (&2:int) (ival nbits))`;;

let gbitsq_reduced_result = new_definition
  `gbitsq_reduced_result
      (p:gbitsq_ptr) (pn:int32) (bi:int32) (nbits:int32)
      (dividend:int) (divisor:int) <=>
     ~(divisor = (&0:int)) /\
     gbitsq_uint64_in_bounds (dividend rem divisor) /\
     (!result:int64.
        gbitsq_u64 result = dividend rem divisor
        ==> gbitsq_result_postcondition p pn bi nbits result)`;;

let gbitsq_small_branch = new_definition
  `gbitsq_small_branch
      (p:gbitsq_ptr) (pn:int32) (bi:int32) (nbits:int32) <=>
     (&0:int) <= ival bi /\
     (!o1:int64.
        gbitsq_u64 o1 = ival bi
        ==>
        (((&0:int) <= gbitsq_u64 o1 /\
          gbitsq_u64 o1 < (&64:int)) /\
         gbitsq_ipow (&2:int) (gbitsq_u64 o1) *
           gbitsq_u64 (word 1:int64) <=
           (&18446744073709551615:int)) /\
        (!o2:int64.
           gbitsq_u64 o2 =
             gbitsq_ipow (&2:int) (gbitsq_u64 o1) *
             gbitsq_u64 (word 1:int64)
           ==>
           (gbitsq_minimum p <= gbitsq_offset p /\
            gbitsq_offset p < gbitsq_maximum p) /\
           gbitsq_reduced_result p pn bi nbits
             (gbitsq_u64 (gbitsq_pelts p (gbitsq_offset p)))
             (gbitsq_u64 o2)))`;;

let gbitsq_one_limb_branch = new_definition
  `gbitsq_one_limb_branch
      (p:gbitsq_ptr) (pn:int32) (bi:int32) (nbits:int32)
      (shifted:int64) <=>
     (&0:int) <= ival nbits /\
     (!o7:int64.
        gbitsq_u64 o7 = ival nbits
        ==>
        (((&0:int) <= gbitsq_u64 o7 /\
          gbitsq_u64 o7 < (&64:int)) /\
         gbitsq_ipow (&2:int) (gbitsq_u64 o7) *
           gbitsq_u64 (word 1:int64) <=
           (&18446744073709551615:int)) /\
        (!o8:int64.
           gbitsq_u64 o8 =
             gbitsq_ipow (&2:int) (gbitsq_u64 o7) *
             gbitsq_u64 (word 1:int64)
           ==>
           gbitsq_reduced_result p pn bi nbits
             (gbitsq_u64 shifted) (gbitsq_u64 o8)))`;;

let gbitsq_two_limb_branch = new_definition
  `gbitsq_two_limb_branch
      (p:gbitsq_ptr) (pn:int32) (bi:int32) (nbits:int32)
      (quotient:int32) (shifted:int64) (remaining:int32) <=>
     gbitsq_int32_in_bounds (ival quotient + (&1:int)) /\
     (!o7:int32.
        ival o7 = ival quotient + (&1:int)
        ==>
        (gbitsq_minimum p <= gbitsq_offset p + ival o7 /\
         gbitsq_offset p + ival o7 < gbitsq_maximum p) /\
        (&0:int) <= ival remaining /\
        (!o8:int64.
           gbitsq_u64 o8 = ival remaining
           ==>
           ((&0:int) <= gbitsq_u64 o8 /\
            gbitsq_u64 o8 < (&64:int)) /\
           (!prs:int64.
              gbitsq_u64 prs =
                (gbitsq_u64
                   (gbitsq_pelts p (gbitsq_offset p + ival o7)) *
                 gbitsq_ipow (&2:int) (gbitsq_u64 o8)) rem
                gbitsq_radix /\
              gbitsq_u64 prs <=
                gbitsq_radix -
                gbitsq_ipow (&2:int) (gbitsq_u64 o8)
              ==>
              gbitsq_int32_in_bounds (ival quotient + (&2:int)) /\
              (!o9:int32.
                 ival o9 = ival quotient + (&2:int)
                 ==>
                 (gbitsq_minimum p <= gbitsq_offset p + ival o9 /\
                  gbitsq_offset p + ival o9 <= gbitsq_maximum p) /\
                 (!p'':gbitsq_ptr.
                    gbitsq_shifted_pointer p'' p (ival o9)
                    ==>
                    ~(gbitsq_radix = (&0:int)) /\
                    gbitsq_uint64_in_bounds
                      (gbitsq_u64 shifted + gbitsq_u64 prs) /\
                    (!o10:int64.
                       gbitsq_u64 o10 =
                         gbitsq_u64 shifted + gbitsq_u64 prs
                       ==>
                       (&0:int) <= ival nbits /\
                       (!o11:int64.
                          gbitsq_u64 o11 = ival nbits
                          ==>
                          (((&0:int) <= gbitsq_u64 o11 /\
                            gbitsq_u64 o11 < (&64:int)) /\
                           gbitsq_ipow (&2:int) (gbitsq_u64 o11) *
                             gbitsq_u64 (word 1:int64) <=
                             (&18446744073709551615:int)) /\
                          (!o12:int64.
                             gbitsq_u64 o12 =
                               gbitsq_ipow (&2:int) (gbitsq_u64 o11) *
                               gbitsq_u64 (word 1:int64)
                             ==>
                             gbitsq_reduced_result p pn bi nbits
                               (gbitsq_u64 o10)
                               (gbitsq_u64 o12)))))))))`;;

let gbitsq_large_branch = new_definition
  `gbitsq_large_branch
      (p:gbitsq_ptr) (pn:int32) (bi:int32) (nbits:int32) <=>
     gbitsq_int32_in_bounds (ival bi - ival nbits) /\
     (!difference:int32.
        ival difference = ival bi - ival nbits
        ==>
        (~((&64:int) = (&0:int)) /\
         gbitsq_int32_in_bounds (ival difference div (&64:int))) /\
        (!quotient:int32.
           ival quotient = ival difference div (&64:int)
           ==>
           (~((&64:int) = (&0:int)) /\
            gbitsq_int32_in_bounds (ival difference rem (&64:int))) /\
           (!remainder:int32.
              ival remainder = ival difference rem (&64:int)
              ==>
              (gbitsq_minimum p <=
                 gbitsq_offset p + ival quotient /\
               gbitsq_offset p + ival quotient <
                 gbitsq_maximum p) /\
              gbitsq_int32_in_bounds (ival quotient + (&1:int)) /\
              (!o4:int32.
                 ival o4 = ival quotient + (&1:int)
                 ==>
                 (gbitsq_minimum p <= gbitsq_offset p + ival o4 /\
                  gbitsq_offset p + ival o4 <= gbitsq_maximum p) /\
                 (!p':gbitsq_ptr.
                    gbitsq_shifted_pointer p' p (ival o4)
                    ==>
                    (&0:int) <= ival remainder /\
                    (!o5:int64.
                       gbitsq_u64 o5 = ival remainder
                       ==>
                       ((&0:int) <= gbitsq_u64 o5 /\
                        gbitsq_u64 o5 < (&64:int)) /\
                       (!shifted:int64.
                          gbitsq_u64 shifted =
                            gbitsq_u64
                              (gbitsq_pelts p
                                (gbitsq_offset p + ival quotient)) div
                            gbitsq_ipow (&2:int) (gbitsq_u64 o5)
                          ==>
                          ~(gbitsq_ipow (&2:int) (ival remainder) =
                            (&0:int)) /\
                          gbitsq_int32_in_bounds
                            ((&64:int) - ival remainder) /\
                          (!remaining:int32.
                             ival remaining =
                               (&64:int) - ival remainder
                             ==>
                             if ival remaining < ival nbits
                             then
                               gbitsq_two_limb_branch
                                 p pn bi nbits quotient shifted remaining
                             else
                               gbitsq_one_limb_branch
                                 p pn bi nbits shifted))))))))`;;

let statement =
  `!nbits:int32. !bi:int32. !pn:int32. !p:gbitsq_ptr.
     ((&1:int) <= ival nbits /\
      ival nbits < (&64:int) /\
      (&0:int) <= ival bi /\
      (&1:int) <= ival pn /\
      gbitsq_valid p (ival pn) /\
      (ival bi + (&63:int)) div (&64:int) <= ival pn)
     ==>
     if ival bi < ival nbits
     then gbitsq_small_branch p pn bi nbits
     else gbitsq_large_branch p pn bi nbits`;;
