(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_limb_size_in_base_2qtvc:
  the verification condition relating a positive unsigned 64-bit limb,
  its 32-bit count of leading zeros, and the resulting binary digit count
  and power-of-two bounds. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory wordsTheory;

val base_info_BaseInfo_wmpn_limb_size_in_base_2qtvc_statement =
  ``!u : word64.
      (0 : int) < &(w2n u) ==>
      (0 : int) < &(w2n u) /\
      (!o1 : word32.
         (2 : int) ** Num (w2i o1) * &(w2n u) <=
             (18446744073709551615 : int) /\
         (18446744073709551615 : int) <
             (2 : int) * (2 : int) ** Num (w2i o1) * &(w2n u) /\
         (0 : int) <= w2i o1 /\
         w2i o1 < (64 : int)
         ==>
         (0 : int) <= w2i o1 /\
         (!shift : word64.
            &(w2n shift) = w2i o1
            ==>
            ((0 : int) <= (64 : int) - &(w2n shift) /\
             (64 : int) - &(w2n shift) <=
               (18446744073709551615 : int)) /\
            (!r : word64.
               &(w2n r) = (64 : int) - &(w2n shift)
               ==>
               ((1 : int) <= &(w2n r) /\
                &(w2n r) <= (64 : int)) /\
               (2 : int) ** Num (&(w2n r) - (1 : int)) <=
                 &(w2n u) /\
               &(w2n u) <
                 (2 : int) ** Num (&(w2n r)))))``;
