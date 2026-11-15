(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/powm_Powm_binvert_limbqtvc: the verification
  condition for computing the modular inverse of an odd 64-bit limb from
  an eight-bit table seed and three precision-doubling Newton updates.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory wordsTheory;

val powm_binvert_radix_def = Define `
  powm_binvert_radix = (18446744073709551616 : int)`;

val powm_binvert_to_num_def = Define `
  powm_binvert_to_num (z : int) =
    if z < (0 : int) then 0 else Num z`;

val powm_binvert_uint_def = Define `
  powm_binvert_uint (x : word64) = &(w2n x)`;

val powm_binvert_ipow_def = Define `
  powm_binvert_ipow (base : int) (exponent : int) =
    base ** powm_binvert_to_num exponent`;

val powm_binvert_uint64_in_bounds_def = Define `
  powm_binvert_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val powm_Powm_binvert_limbqtvc_statement =
  ``!n : word64.
      ODD (w2n n)
      ==>
      (!n1 inv prec : int.
         (((0 : int) <= n1 /\ (0 : int) <= inv) /\
          (inv * n1) %
              powm_binvert_ipow (2 : int) prec =
            (1 : int) /\
          (0 : int) <= (2 : int) * prec /\
          (2 : int) * prec <= (64 : int))
         ==>
         ((((2 : int) * inv - inv * (inv * n1)) %
              powm_binvert_radix) *
             n1) %
             powm_binvert_ipow
               (2 : int) ((2 : int) * prec) =
           (1 : int)) /\
      ~((2 : int) = (0 : int)) /\
      powm_binvert_uint64_in_bounds
        (powm_binvert_uint n / (2 : int)) /\
      (!o1 : word64.
         powm_binvert_uint o1 =
           powm_binvert_uint n / (2 : int)
         ==>
         (~((128 : int) = (0 : int)) /\
          powm_binvert_uint64_in_bounds
            (powm_binvert_uint o1 % (128 : int))) /\
         (!h : word64.
            powm_binvert_uint h =
              powm_binvert_uint o1 % (128 : int)
            ==>
            ((0 : int) <= powm_binvert_uint h /\
             powm_binvert_uint h < (128 : int)) /\
            (!o2 : word64.
               (((0 : int) <= powm_binvert_uint o2 /\
                 powm_binvert_uint o2 < (256 : int)) /\
                (powm_binvert_uint o2 *
                   ((2 : int) * powm_binvert_uint h + (1 : int))) %
                    powm_binvert_ipow (2 : int) (8 : int) =
                  (1 : int))
               ==>
               (!o3 : word64.
                  powm_binvert_uint o3 =
                    (powm_binvert_uint o2 *
                       powm_binvert_uint n) %
                      powm_binvert_radix
                  ==>
                  (!o4 : word64.
                     powm_binvert_uint o4 =
                       (powm_binvert_uint o2 *
                          powm_binvert_uint o3) %
                         powm_binvert_radix
                     ==>
                     (!o5 : word64.
                        powm_binvert_uint o5 =
                          ((2 : int) * powm_binvert_uint o2) %
                            powm_binvert_radix
                        ==>
                        (!o6 : word64.
                           powm_binvert_uint o6 =
                             (powm_binvert_uint o5 -
                                powm_binvert_uint o4) %
                               powm_binvert_radix
                           ==>
                           (!o7 : word64.
                              powm_binvert_uint o7 =
                                (powm_binvert_uint o6 *
                                   powm_binvert_uint n) %
                                  powm_binvert_radix
                              ==>
                              (!o8 : word64.
                                 powm_binvert_uint o8 =
                                   (powm_binvert_uint o6 *
                                      powm_binvert_uint o7) %
                                     powm_binvert_radix
                                 ==>
                                 (!o9 : word64.
                                    powm_binvert_uint o9 =
                                      ((2 : int) *
                                         powm_binvert_uint o6) %
                                        powm_binvert_radix
                                    ==>
                                    (!o10 : word64.
                                       powm_binvert_uint o10 =
                                         (powm_binvert_uint o9 -
                                            powm_binvert_uint o8) %
                                           powm_binvert_radix
                                       ==>
                                       (!o11 : word64.
                                          powm_binvert_uint o11 =
                                            (powm_binvert_uint o10 *
                                               powm_binvert_uint n) %
                                              powm_binvert_radix
                                          ==>
                                          (!o12 : word64.
                                             powm_binvert_uint o12 =
                                               (powm_binvert_uint o10 *
                                                  powm_binvert_uint o11) %
                                                 powm_binvert_radix
                                             ==>
                                             (!o13 : word64.
                                                powm_binvert_uint o13 =
                                                  ((2 : int) *
                                                     powm_binvert_uint o10) %
                                                    powm_binvert_radix
                                                ==>
                                                (!o14 : word64.
                                                   powm_binvert_uint o14 =
                                                     (powm_binvert_uint o13 -
                                                        powm_binvert_uint o12) %
                                                       powm_binvert_radix
                                                   ==>
                                                   (powm_binvert_uint o14 *
                                                      powm_binvert_uint n) %
                                                       powm_binvert_radix =
                                                     (1 : int))))))))))))))))``;
