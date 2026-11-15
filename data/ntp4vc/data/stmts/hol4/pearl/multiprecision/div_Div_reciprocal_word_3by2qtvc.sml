(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_reciprocal_word_3by2qtvc: the verification
  condition for computing a reciprocal approximation for a normalized
  two-limb 64-bit divisor, including the carry, borrow, product, and final
  quotient-correction branches. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory wordsTheory;

val reciprocal_word_3by2_radix_def = Define `
  reciprocal_word_3by2_radix = (18446744073709551616 : int)`;

val reciprocal_word_3by2_uint_def = Define `
  reciprocal_word_3by2_uint (x : word64) = &(w2n x)`;

val reciprocal_word_3by2_uint64_in_bounds_def = Define `
  reciprocal_word_3by2_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val reciprocal_word_3by2_reciprocal_def = Define `
  reciprocal_word_3by2_reciprocal
      (v : word64) (d : word64) <=>
    reciprocal_word_3by2_uint v =
      (reciprocal_word_3by2_radix *
         reciprocal_word_3by2_radix - (1 : int)) /
        reciprocal_word_3by2_uint d -
      reciprocal_word_3by2_radix`;

val reciprocal_word_3by2_reciprocal_3by2_def = Define `
  reciprocal_word_3by2_reciprocal_3by2
      (v : word64) (dh : word64) (dl : word64) <=>
    reciprocal_word_3by2_uint v =
      (reciprocal_word_3by2_radix *
         reciprocal_word_3by2_radix *
         reciprocal_word_3by2_radix - (1 : int)) /
        (reciprocal_word_3by2_uint dl +
         reciprocal_word_3by2_radix *
           reciprocal_word_3by2_uint dh) -
      reciprocal_word_3by2_radix`;

val div_Div_reciprocal_word_3by2qtvc_statement =
  ``!dh dl : word64.
      reciprocal_word_3by2_radix / (2 : int) <=
        reciprocal_word_3by2_uint dh
      ==>
      reciprocal_word_3by2_radix / (2 : int) <=
        reciprocal_word_3by2_uint dh /\
      (!o1 : word64.
         reciprocal_word_3by2_reciprocal o1 dh
         ==>
         (!o2 : word64.
            reciprocal_word_3by2_uint o2 =
              (reciprocal_word_3by2_uint dh *
               reciprocal_word_3by2_uint o1) %
                reciprocal_word_3by2_radix
            ==>
            (!o3 : word64.
               reciprocal_word_3by2_uint o3 =
                 (reciprocal_word_3by2_uint o2 +
                  reciprocal_word_3by2_uint dl) %
                   reciprocal_word_3by2_radix
               ==>
               if reciprocal_word_3by2_uint o3 <
                  reciprocal_word_3by2_uint dl
               then
                 if reciprocal_word_3by2_uint dh <=
                    reciprocal_word_3by2_uint o3
                 then
                   reciprocal_word_3by2_uint64_in_bounds
                     (reciprocal_word_3by2_uint o1 - (1 : int)) /\
                   (!o4 : word64.
                      reciprocal_word_3by2_uint o4 =
                        reciprocal_word_3by2_uint o1 - (1 : int)
                      ==>
                      reciprocal_word_3by2_uint64_in_bounds
                        (reciprocal_word_3by2_uint o3 -
                         reciprocal_word_3by2_uint dh) /\
                      (!o5 : word64.
                         reciprocal_word_3by2_uint o5 =
                           reciprocal_word_3by2_uint o3 -
                             reciprocal_word_3by2_uint dh
                         ==>
                         reciprocal_word_3by2_uint64_in_bounds
                           (reciprocal_word_3by2_uint o4 - (1 : int)) /\
                         (!o6 : word64.
                            reciprocal_word_3by2_uint o6 =
                              reciprocal_word_3by2_uint o4 - (1 : int)
                            ==>
                            (!o7 : word64.
                               reciprocal_word_3by2_uint o7 =
                                 (reciprocal_word_3by2_uint o5 -
                                  reciprocal_word_3by2_uint dh) %
                                   reciprocal_word_3by2_radix
                               ==>
                               (!tl th : word64.
                                  reciprocal_word_3by2_uint tl +
                                      reciprocal_word_3by2_radix *
                                        reciprocal_word_3by2_uint th =
                                    reciprocal_word_3by2_uint o6 *
                                      reciprocal_word_3by2_uint dl
                                  ==>
                                  (!o8 : word64.
                                     reciprocal_word_3by2_uint o8 =
                                       (reciprocal_word_3by2_uint o7 +
                                        reciprocal_word_3by2_uint th) %
                                         reciprocal_word_3by2_radix
                                     ==>
                                     if reciprocal_word_3by2_uint o8 <
                                        reciprocal_word_3by2_uint th
                                     then
                                       (!o9 : bool.
                                          (if reciprocal_word_3by2_uint dh <
                                              reciprocal_word_3by2_uint o8
                                           then
                                             o9 = T
                                           else
                                             ?o10 : bool.
                                               ((reciprocal_word_3by2_uint o8 =
                                                   reciprocal_word_3by2_uint dh
                                                 ==> o10 = T) /\
                                                (o10 = T ==> o8 = dh)) /\
                                               (if o10 = T
                                                then
                                                  o9 =
                                                    (if reciprocal_word_3by2_uint dl <=
                                                        reciprocal_word_3by2_uint tl
                                                     then T
                                                     else F)
                                                else
                                                  o9 = F))
                                          ==>
                                          if o9 = T
                                          then
                                            reciprocal_word_3by2_uint64_in_bounds
                                              (reciprocal_word_3by2_uint o6 -
                                               (1 : int)) /\
                                            (!o10 : word64.
                                               reciprocal_word_3by2_uint o10 =
                                                 reciprocal_word_3by2_uint o6 -
                                                   (1 : int)
                                               ==>
                                               reciprocal_word_3by2_uint64_in_bounds
                                                 (reciprocal_word_3by2_uint o10 -
                                                  (1 : int)) /\
                                               (!o11 : word64.
                                                  reciprocal_word_3by2_uint o11 =
                                                    reciprocal_word_3by2_uint o10 -
                                                      (1 : int)
                                                  ==>
                                                  reciprocal_word_3by2_reciprocal_3by2
                                                    o11 dh dl))
                                          else
                                            reciprocal_word_3by2_uint64_in_bounds
                                              (reciprocal_word_3by2_uint o6 -
                                               (1 : int)) /\
                                            (!o10 : word64.
                                               reciprocal_word_3by2_uint o10 =
                                                 reciprocal_word_3by2_uint o6 -
                                                   (1 : int)
                                               ==>
                                               reciprocal_word_3by2_reciprocal_3by2
                                                 o10 dh dl))
                                     else
                                       reciprocal_word_3by2_reciprocal_3by2
                                         o6 dh dl))))))
                 else
                   reciprocal_word_3by2_uint64_in_bounds
                     (reciprocal_word_3by2_uint o1 - (1 : int)) /\
                   (!o4 : word64.
                      reciprocal_word_3by2_uint o4 =
                        reciprocal_word_3by2_uint o1 - (1 : int)
                      ==>
                      (!o5 : word64.
                         reciprocal_word_3by2_uint o5 =
                           (reciprocal_word_3by2_uint o3 -
                            reciprocal_word_3by2_uint dh) %
                             reciprocal_word_3by2_radix
                         ==>
                         (!tl th : word64.
                            reciprocal_word_3by2_uint tl +
                                reciprocal_word_3by2_radix *
                                  reciprocal_word_3by2_uint th =
                              reciprocal_word_3by2_uint o4 *
                                reciprocal_word_3by2_uint dl
                            ==>
                            (!o6 : word64.
                               reciprocal_word_3by2_uint o6 =
                                 (reciprocal_word_3by2_uint o5 +
                                  reciprocal_word_3by2_uint th) %
                                   reciprocal_word_3by2_radix
                               ==>
                               if reciprocal_word_3by2_uint o6 <
                                  reciprocal_word_3by2_uint th
                               then
                                 (!o7 : bool.
                                    (if reciprocal_word_3by2_uint dh <
                                        reciprocal_word_3by2_uint o6
                                     then
                                       o7 = T
                                     else
                                       ?o8 : bool.
                                         ((reciprocal_word_3by2_uint o6 =
                                             reciprocal_word_3by2_uint dh
                                           ==> o8 = T) /\
                                          (o8 = T ==> o6 = dh)) /\
                                         (if o8 = T
                                          then
                                            o7 =
                                              (if reciprocal_word_3by2_uint dl <=
                                                  reciprocal_word_3by2_uint tl
                                               then T
                                               else F)
                                          else
                                            o7 = F))
                                    ==>
                                    if o7 = T
                                    then
                                      reciprocal_word_3by2_uint64_in_bounds
                                        (reciprocal_word_3by2_uint o4 -
                                         (1 : int)) /\
                                      (!o8 : word64.
                                         reciprocal_word_3by2_uint o8 =
                                           reciprocal_word_3by2_uint o4 -
                                             (1 : int)
                                         ==>
                                         reciprocal_word_3by2_uint64_in_bounds
                                           (reciprocal_word_3by2_uint o8 -
                                            (1 : int)) /\
                                         (!o9 : word64.
                                            reciprocal_word_3by2_uint o9 =
                                              reciprocal_word_3by2_uint o8 -
                                                (1 : int)
                                            ==>
                                            reciprocal_word_3by2_reciprocal_3by2
                                              o9 dh dl))
                                    else
                                      reciprocal_word_3by2_uint64_in_bounds
                                        (reciprocal_word_3by2_uint o4 -
                                         (1 : int)) /\
                                      (!o8 : word64.
                                         reciprocal_word_3by2_uint o8 =
                                           reciprocal_word_3by2_uint o4 -
                                             (1 : int)
                                         ==>
                                         reciprocal_word_3by2_reciprocal_3by2
                                           o8 dh dl))
                               else
                                 reciprocal_word_3by2_reciprocal_3by2
                                   o4 dh dl))))
               else
                 (!tl th : word64.
                    reciprocal_word_3by2_uint tl +
                        reciprocal_word_3by2_radix *
                          reciprocal_word_3by2_uint th =
                      reciprocal_word_3by2_uint o1 *
                        reciprocal_word_3by2_uint dl
                    ==>
                    (!o4 : word64.
                       reciprocal_word_3by2_uint o4 =
                         (reciprocal_word_3by2_uint o3 +
                          reciprocal_word_3by2_uint th) %
                           reciprocal_word_3by2_radix
                       ==>
                       if reciprocal_word_3by2_uint o4 <
                          reciprocal_word_3by2_uint th
                       then
                         (!o5 : bool.
                            (if reciprocal_word_3by2_uint dh <
                                reciprocal_word_3by2_uint o4
                             then
                               o5 = T
                             else
                               ?o6 : bool.
                                 ((reciprocal_word_3by2_uint o4 =
                                     reciprocal_word_3by2_uint dh
                                   ==> o6 = T) /\
                                  (o6 = T ==> o4 = dh)) /\
                                 (if o6 = T
                                  then
                                    o5 =
                                      (if reciprocal_word_3by2_uint dl <=
                                          reciprocal_word_3by2_uint tl
                                       then T
                                       else F)
                                  else
                                    o5 = F))
                            ==>
                            if o5 = T
                            then
                              reciprocal_word_3by2_uint64_in_bounds
                                (reciprocal_word_3by2_uint o1 - (1 : int)) /\
                              (!o6 : word64.
                                 reciprocal_word_3by2_uint o6 =
                                   reciprocal_word_3by2_uint o1 - (1 : int)
                                 ==>
                                 reciprocal_word_3by2_uint64_in_bounds
                                   (reciprocal_word_3by2_uint o6 - (1 : int)) /\
                                 (!o7 : word64.
                                    reciprocal_word_3by2_uint o7 =
                                      reciprocal_word_3by2_uint o6 - (1 : int)
                                    ==>
                                    reciprocal_word_3by2_reciprocal_3by2
                                      o7 dh dl))
                            else
                              reciprocal_word_3by2_uint64_in_bounds
                                (reciprocal_word_3by2_uint o1 - (1 : int)) /\
                              (!o6 : word64.
                                 reciprocal_word_3by2_uint o6 =
                                   reciprocal_word_3by2_uint o1 - (1 : int)
                                 ==>
                                 reciprocal_word_3by2_reciprocal_3by2
                                   o6 dh dl))
                       else
                         reciprocal_word_3by2_reciprocal_3by2
                           o1 dh dl)))))``;
