(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/there_and_back_again_Convolution_convolutionqtvc: the top-level
  symbolic-convolution verification condition for equal-length lists,
  identifying the first list paired elementwise with the reversed second
  list. This file contains no proof.
*)

open HolKernel Parse boolLib;
open listTheory pairTheory;

val there_and_back_again_Convolution_convolution_vc =
  ``!x y : 'a list.
      LENGTH x = LENGTH y ==>
      LENGTH x <= LENGTH y /\
      !o1 : ('a # 'a) list.
      !o2 : 'a list.
        (?y0 : 'a list.
           y = APPEND y0 o2 /\
           LENGTH y0 = LENGTH x /\
           o1 = ZIP (x, REVERSE y0)) ==>
        o1 = ZIP (x, REVERSE y)``;
