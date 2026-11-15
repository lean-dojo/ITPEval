(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_getbitqtvc: the verification condition for
  extracting one bit from a multiprecision integer and relating it to the
  recurrence for the value of its low-bit prefix. This file contains no proof.
*)

needs "Library/words.ml";;
needs "Library/isum.ml";;

new_type_abbrev
  ("gbq_ptr",`:(int64 list)#(int#(int#(int#(bool#Z))))`);;

let gbq_radix = new_definition
  `gbq_radix = (&18446744073709551616:int)`;;

let gbq_u64 = new_definition
  `gbq_u64 (x:int64) = (&(val x):int)`;;

let gbq_int32_in_bounds = new_definition
  `gbq_int32_in_bounds (x:int) <=>
     --(&2147483648:int) <= x /\ x <= (&2147483647:int)`;;

let gbq_uint64_in_bounds = new_definition
  `gbq_uint64_in_bounds (x:int) <=>
     (&0:int) <= x /\ x <= (&18446744073709551615:int)`;;

let gbq_ipow = new_definition
  `gbq_ipow (base:int) (exponent:int) =
     base pow (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let gbq_data = new_definition
  `gbq_data (p:gbq_ptr) = FST p`;;

let gbq_offset = new_definition
  `gbq_offset (p:gbq_ptr) = FST (SND p)`;;

let gbq_minimum = new_definition
  `gbq_minimum (p:gbq_ptr) = FST (SND (SND p))`;;

let gbq_maximum = new_definition
  `gbq_maximum (p:gbq_ptr) = FST (SND (SND (SND p)))`;;

let gbq_writable = new_definition
  `gbq_writable (p:gbq_ptr) =
     FST (SND (SND (SND (SND p))))`;;

let gbq_zone = new_definition
  `gbq_zone (p:gbq_ptr) =
     SND (SND (SND (SND (SND p))))`;;

let gbq_pelts = new_definition
  `gbq_pelts p (i:int) =
     let k = if i < (&0:int) then 0 else num_of_int i in
     if k < LENGTH (gbq_data p)
     then EL k (gbq_data p)
     else (word 0:int64)`;;

let gbq_plength = new_definition
  `gbq_plength p = (&(LENGTH (gbq_data p)):int)`;;

let gbq_valid = new_definition
  `gbq_valid p (size:int) <=>
     gbq_int32_in_bounds size /\
     (&0:int) <= size /\
     (&0:int) <= gbq_minimum p /\
     gbq_minimum p <= gbq_offset p /\
     gbq_offset p + size <= gbq_maximum p /\
     gbq_maximum p <= gbq_plength p`;;

let gbq_value = new_definition
  `gbq_value p (size:int) =
     if size <= (&0:int) then (&0:int)
     else
       isum (0..num_of_int size - 1)
         (\k. gbq_radix pow k *
              gbq_u64 (gbq_pelts p (gbq_offset p + &k)))`;;

let gbq_valueb = new_definition
  `gbq_valueb p (nbits:int) =
     if nbits < (&0:int) then (&0:int)
     else
       let i = nbits div (&64:int) in
       gbq_value p i +
       gbq_ipow gbq_radix i *
         (gbq_u64 (gbq_pelts p (gbq_offset p + i)) rem
          gbq_ipow (&2:int) (nbits - (&64:int) * i))`;;

let gbq_shifted_pointer = new_definition
  `gbq_shifted_pointer shifted base (displacement:int) <=>
     gbq_offset shifted = gbq_offset base + displacement /\
     gbq_plength shifted = gbq_plength base /\
     gbq_pelts shifted = gbq_pelts base /\
     gbq_data shifted = gbq_data base /\
     gbq_minimum shifted = gbq_minimum base /\
     gbq_maximum shifted = gbq_maximum base /\
     gbq_zone shifted = gbq_zone base /\
     gbq_writable shifted = gbq_writable base`;;

let statement =
  `!p:gbq_ptr. !pn:int32. !bi:int32.
     gbq_valid p (ival pn) /\
     (&1:int) <= ival bi /\
     (ival bi + (&63:int)) div (&64:int) <= ival pn
     ==>
     gbq_int32_in_bounds (ival bi - (&1:int)) /\
     (!o1:int32.
        ival o1 = ival bi - (&1:int)
        ==>
        (~((&64:int) = (&0:int)) /\
         gbq_int32_in_bounds (ival o1 div (&64:int))) /\
        (!i:int32.
           ival i = ival o1 div (&64:int)
           ==>
           gbq_int32_in_bounds (ival bi - (&1:int)) /\
           (!o2:int32.
              ival o2 = ival bi - (&1:int)
              ==>
              (&0:int) <= ival o2 /\
              (!o3:int64.
                 gbq_u64 o3 = ival o2
                 ==>
                 (~((&64:int) = (&0:int)) /\
                  gbq_uint64_in_bounds
                    (gbq_u64 o3 rem (&64:int))) /\
                 (!mi:int64.
                    gbq_u64 mi = gbq_u64 o3 rem (&64:int)
                    ==>
                    (gbq_minimum p <= gbq_offset p + ival i /\
                     gbq_offset p + ival i < gbq_maximum p) /\
                    gbq_int32_in_bounds (ival i + (&1:int)) /\
                    (!o4:int32.
                       ival o4 = ival i + (&1:int)
                       ==>
                       (gbq_minimum p <= gbq_offset p + ival o4 /\
                        gbq_offset p + ival o4 <= gbq_maximum p) /\
                       (!p':gbq_ptr.
                          gbq_shifted_pointer p' p (ival o4)
                          ==>
                          ((&0:int) <= gbq_u64 mi /\
                           gbq_u64 mi < (&64:int)) /\
                          (!lps:int64.
                             gbq_u64 lps =
                               gbq_u64
                                 (gbq_pelts p
                                   (gbq_offset p + ival i)) div
                               gbq_ipow (&2:int) (gbq_u64 mi)
                             ==>
                             ~(gbq_ipow (&2:int) (gbq_u64 mi) =
                               (&0:int)) /\
                             (~((&2:int) = (&0:int)) /\
                              gbq_uint64_in_bounds
                                (gbq_u64 lps rem (&2:int))) /\
                             (!res:int64.
                                gbq_u64 res =
                                  gbq_u64 lps rem (&2:int)
                                ==>
                                ~((&2:int) = (&0:int)) /\
                                (~((&2:int) = (&0:int)) /\
                                 gbq_uint64_in_bounds
                                   (gbq_u64 lps rem (&2:int))) /\
                                (!result:int64.
                                   gbq_u64 result =
                                     gbq_u64 lps rem (&2:int)
                                   ==>
                                   ((&0:int) <= gbq_u64 result /\
                                    gbq_u64 result <= (&1:int)) /\
                                   gbq_u64 result =
                                     (gbq_value p (ival pn) div
                                      gbq_ipow (&2:int)
                                        (ival bi - (&1:int))) rem
                                     (&2:int) /\
                                   gbq_valueb p (ival bi) =
                                     gbq_valueb p
                                       (ival bi - (&1:int)) +
                                     gbq_ipow (&2:int)
                                       (ival bi - (&1:int)) *
                                     gbq_u64 result))))))))))`;;
