(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_base_power_of_two_pqtvc:
  the verification condition for recognizing powers of two from 2 through
  256 and returning their exponents as an unsigned 32-bit result. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory wordsTheory;

val base_info_BaseInfo_wmpn_base_power_of_two_pqtvc_statement =
  ``!b : word64.
    !o1 : bool.
    !result : word32.
      (2 : int) <= &(w2n b) ==>
      &(w2n b) <= (256 : int) ==>
      (&(w2n b) = &(w2n (2w : word64)) ==> o1 = T) ==>
      (o1 = T ==> b = (2w : word64)) ==>
      (if o1 = T then
         result = (1w : word32)
       else
         (?o2 : bool.
            ((&(w2n b) = &(w2n (4w : word64)) ==> o2 = T) /\
             (o2 = T ==> b = (4w : word64))) /\
            (if o2 = T then
               result = (2w : word32)
             else
               (?o3 : bool.
                  ((&(w2n b) = &(w2n (8w : word64)) ==> o3 = T) /\
                   (o3 = T ==> b = (8w : word64))) /\
                  (if o3 = T then
                     result = (3w : word32)
                   else
                     (?o4 : bool.
                        ((&(w2n b) = &(w2n (16w : word64)) ==>
                            o4 = T) /\
                         (o4 = T ==> b = (16w : word64))) /\
                        (if o4 = T then
                           result = (4w : word32)
                         else
                           (?o5 : bool.
                              ((&(w2n b) =
                                   &(w2n (32w : word64)) ==>
                                  o5 = T) /\
                               (o5 = T ==> b = (32w : word64))) /\
                              (if o5 = T then
                                 result = (5w : word32)
                               else
                                 (?o6 : bool.
                                    ((&(w2n b) =
                                         &(w2n (64w : word64)) ==>
                                        o6 = T) /\
                                     (o6 = T ==>
                                        b = (64w : word64))) /\
                                    (if o6 = T then
                                       result = (6w : word32)
                                     else
                                       (?o7 : bool.
                                          ((&(w2n b) =
                                               &(w2n
                                                   (128w : word64)) ==>
                                              o7 = T) /\
                                           (o7 = T ==>
                                              b = (128w : word64))) /\
                                          (if o7 = T then
                                             result = (7w : word32)
                                           else
                                             (?o8 : bool.
                                                ((&(w2n b) =
                                                     &(w2n
                                                         (256w :
                                                            word64)) ==>
                                                    o8 = T) /\
                                                 (o8 = T ==>
                                                    b =
                                                      (256w :
                                                         word64))) /\
                                                (if o8 = T then
                                                   result =
                                                     (8w : word32)
                                                 else
                                                   result =
                                                     (0w :
                                                        word32))))))))))))))))
      ==>
      (0 : int) <= &(w2n result) /\
      &(w2n result) <= (8 : int) /\
      (~(&(w2n result) = (0 : int)) ==>
       (2 : int) ** w2n result = &(w2n b)) /\
      (&(w2n result) = (0 : int) ==>
       (!n : int.
          (0 : int) <= n ==>
          ~((2 : int) ** Num n = &(w2n b))))``;
