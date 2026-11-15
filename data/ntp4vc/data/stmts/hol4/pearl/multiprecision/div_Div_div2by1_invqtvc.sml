(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/div_Div_div2by1_invqtvc: the verification condition
  for reciprocal-based division of a two-limb unsigned integer by one
  normalized 64-bit limb, including carry and quotient-remainder correction
  branches. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory wordsTheory;

val div2by1_inv_radix_def = Define `
  div2by1_inv_radix = (18446744073709551616 : int)`;

val div2by1_inv_uint_def = Define `
  div2by1_inv_uint (x : word64) = &(w2n x)`;

val div2by1_inv_uint64_in_bounds_def = Define `
  div2by1_inv_uint64_in_bounds (z : int) <=>
    (0 : int) <= z /\ z <= (18446744073709551615 : int)`;

val div2by1_inv_reciprocal_def = Define `
  div2by1_inv_reciprocal (v : word64) (d : word64) <=>
    div2by1_inv_uint v =
      (div2by1_inv_radix * div2by1_inv_radix - (1 : int)) /
        div2by1_inv_uint d -
      div2by1_inv_radix`;

val div2by1_inv_result_def = Define `
  div2by1_inv_result
      (q : word64)
      (r : word64)
      (d : word64)
      (ul : word64)
      (uh : word64) <=>
    div2by1_inv_uint q * div2by1_inv_uint d +
        div2by1_inv_uint r =
      div2by1_inv_uint ul +
        div2by1_inv_radix * div2by1_inv_uint uh /\
    (0 : int) <= div2by1_inv_uint r /\
    div2by1_inv_uint r < div2by1_inv_uint d`;

val div_Div_div2by1_invqtvc_statement =
  ``!d uh v l h ul : word64.
      div2by1_inv_radix / (2 : int) <= div2by1_inv_uint d ==>
      div2by1_inv_uint uh < div2by1_inv_uint d ==>
      div2by1_inv_reciprocal v d ==>
      div2by1_inv_uint l +
          div2by1_inv_radix * div2by1_inv_uint h =
        div2by1_inv_uint v * div2by1_inv_uint uh
      ==>
      (0 : int) <= (0 : int) /\
      (0 : int) <= (1 : int) /\
      (!sl c : word64.
         div2by1_inv_uint sl +
             div2by1_inv_radix * div2by1_inv_uint c =
           div2by1_inv_uint l + div2by1_inv_uint ul + (0 : int) /\
         (0 : int) <= div2by1_inv_uint c /\
         div2by1_inv_uint c <= (1 : int)
         ==>
         ((0 : int) <= div2by1_inv_uint c /\
          div2by1_inv_uint c <= (1 : int)) /\
         (!sh c' : word64.
            div2by1_inv_uint sh +
                div2by1_inv_radix * div2by1_inv_uint c' =
              div2by1_inv_uint uh +
                div2by1_inv_uint h +
                div2by1_inv_uint c /\
            (0 : int) <= div2by1_inv_uint c' /\
            div2by1_inv_uint c' <= (1 : int)
            ==>
            (!o1 : word64.
               div2by1_inv_uint o1 =
                 (div2by1_inv_uint sh + (1 : int)) %
                   div2by1_inv_radix
               ==>
               (!p : word64.
                  div2by1_inv_uint p =
                    (div2by1_inv_uint o1 * div2by1_inv_uint d) %
                      div2by1_inv_radix
                  ==>
                  (!o2 : word64.
                     div2by1_inv_uint o2 =
                       (div2by1_inv_uint ul - div2by1_inv_uint p) %
                         div2by1_inv_radix
                     ==>
                     if div2by1_inv_uint sl < div2by1_inv_uint o2 then
                       !o3 : word64.
                         div2by1_inv_uint o3 =
                           (div2by1_inv_uint o1 - (1 : int)) %
                             div2by1_inv_radix
                         ==>
                         (!o4 : word64.
                            div2by1_inv_uint o4 =
                              (div2by1_inv_uint o2 +
                               div2by1_inv_uint d) %
                                div2by1_inv_radix
                            ==>
                            if div2by1_inv_uint d <=
                               div2by1_inv_uint o4
                            then
                              div2by1_inv_uint64_in_bounds
                                (div2by1_inv_uint o3 + (1 : int)) /\
                              (!o5 : word64.
                                 div2by1_inv_uint o5 =
                                   div2by1_inv_uint o3 + (1 : int)
                                 ==>
                                 div2by1_inv_uint64_in_bounds
                                   (div2by1_inv_uint o4 -
                                    div2by1_inv_uint d) /\
                                 (!o6 : word64.
                                    div2by1_inv_uint o6 =
                                      div2by1_inv_uint o4 -
                                        div2by1_inv_uint d
                                    ==>
                                    div2by1_inv_result
                                      o5 o6 d ul uh))
                            else
                              div2by1_inv_result o3 o4 d ul uh)
                     else if div2by1_inv_uint d <=
                             div2by1_inv_uint o2
                     then
                       div2by1_inv_uint64_in_bounds
                         (div2by1_inv_uint o1 + (1 : int)) /\
                       (!o3 : word64.
                          div2by1_inv_uint o3 =
                            div2by1_inv_uint o1 + (1 : int)
                          ==>
                          div2by1_inv_uint64_in_bounds
                            (div2by1_inv_uint o2 -
                             div2by1_inv_uint d) /\
                          (!o4 : word64.
                             div2by1_inv_uint o4 =
                               div2by1_inv_uint o2 -
                                 div2by1_inv_uint d
                             ==>
                             div2by1_inv_result o3 o4 d ul uh))
                     else
                       div2by1_inv_result o1 o2 d ul uh)))))``;
