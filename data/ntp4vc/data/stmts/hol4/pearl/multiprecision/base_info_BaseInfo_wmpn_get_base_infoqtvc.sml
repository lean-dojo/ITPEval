(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_get_base_infoqtvc: the
  verification condition for computing an invariant-bearing multiprecision
  base record by iterating unsigned 64-bit powers up to the quotient of the
  maximum limb by the base. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory wordsTheory;

val get_base_info_uint64_in_bounds_def = Define `
  get_base_info_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val get_base_info_uint32_in_bounds_def = Define `
  get_base_info_uint32_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (4294967295 : int)`;

val get_base_info_cdiv_def = Define `
  get_base_info_cdiv (x : int) (y : int) = x quot y`;

val get_base_info_record_invariant_def = Define `
  get_base_info_record_invariant
      (result : int # (word32 # word64)) <=>
    (2 : int) <= FST result /\
    FST result <= (256 : int) /\
    &(w2n (SND (SND result))) <
      (18446744073709551615 : int) + (1 : int) /\
    (18446744073709551615 : int) + (1 : int) <=
      &(w2n (SND (SND result))) * FST result /\
    (7 : int) <= &(w2n (FST (SND result))) /\
    &(w2n (FST (SND result))) <= (63 : int) /\
    &(w2n (SND (SND result))) =
      FST result ** w2n (FST (SND result))`;

val base_info_BaseInfo_wmpn_get_base_infoqtvc_statement =
  ``!b1 : word64.
      (2 : int) <= &(w2n b1) ==>
      &(w2n b1) <= (256 : int) ==>
      ~(&(w2n b1) = (0 : int)) /\
      get_base_info_uint64_in_bounds
        (get_base_info_cdiv
           (18446744073709551615 : int) (&(w2n b1))) /\
      (!m : word64.
         &(w2n m) =
           get_base_info_cdiv
             (18446744073709551615 : int) (&(w2n b1))
         ==>
         (&(w2n b1) ** 1 = &(w2n b1) /\
          (1 : int) <= (1 : int) /\
          (1 : int) <= (64 : int)) /\
         (!exp1 : word32.
          !p : word64.
            &(w2n b1) ** w2n exp1 = &(w2n p) /\
            (1 : int) <= &(w2n exp1) /\
            &(w2n exp1) <= (64 : int)
            ==>
            if &(w2n p) <= &(w2n m) then
              get_base_info_uint64_in_bounds
                (&(w2n p) * &(w2n b1)) /\
              (!o1 : word64.
                 &(w2n o1) = &(w2n p) * &(w2n b1)
                 ==>
                 get_base_info_uint32_in_bounds
                   (&(w2n exp1) + (1 : int)) /\
                 (!o2 : word32.
                    &(w2n o2) = &(w2n exp1) + (1 : int)
                    ==>
                    ((0 : int) <= &(w2n m) - &(w2n p) /\
                     &(w2n m) - &(w2n o1) <
                       &(w2n m) - &(w2n p)) /\
                    &(w2n b1) ** w2n o2 = &(w2n o1) /\
                    (1 : int) <= &(w2n o2) /\
                    &(w2n o2) <= (64 : int)))
            else
              let o1 = &(w2n b1) in
                ((2 : int) <= o1 /\ o1 <= (256 : int)) /\
                (&(w2n p) <
                   (18446744073709551615 : int) + (1 : int) /\
                 (18446744073709551615 : int) + (1 : int) <=
                   &(w2n p) * o1) /\
                ((7 : int) <= &(w2n exp1) /\
                 &(w2n exp1) <= (63 : int)) /\
                &(w2n p) = o1 ** w2n exp1 /\
                (!result : int # (word32 # word64).
                   get_base_info_record_invariant result
                   ==>
                   FST result = o1 /\
                   FST (SND result) = exp1 /\
                   SND (SND result) = p
                   ==>
                   FST result = &(w2n b1))))``;
