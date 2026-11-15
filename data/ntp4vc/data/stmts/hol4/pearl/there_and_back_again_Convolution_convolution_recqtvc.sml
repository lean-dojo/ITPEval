(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/there_and_back_again_Convolution_convolution_recqtvc: the recursive
  symbolic-convolution verification condition, showing that paired output
  combines the first input list with the reverse of the consumed prefix of
  the second list while returning the unconsumed suffix. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open listTheory pairTheory;

val there_and_back_again_Convolution_convolution_rec_vc =
  ``!x y : 'a list.
      LENGTH x <= LENGTH y ==>
      ((case x of
          [] => T
        | x0::xs =>
            ((case x of
                [] => F
              | h::f => f = xs) /\
             LENGTH xs <= LENGTH y) /\
            (!o1 : ('a # 'a) list.
             !o2 : 'a list.
               (?y0 : 'a list.
                  y = APPEND y0 o2 /\
                  LENGTH y0 = LENGTH xs /\
                  o1 = ZIP (xs, REVERSE y0)) ==>
               (case o2 of
                  [] => F
                | x1::x2 => T))) /\
       (!r : ('a # 'a) list.
        !ys : 'a list.
          (case x of
             [] => r = [] /\ ys = y
           | x0::xs =>
               ?r1 : ('a # 'a) list.
               ?ys1 : 'a list.
                 (?y0 : 'a list.
                    y = APPEND y0 ys1 /\
                    LENGTH y0 = LENGTH xs /\
                    r1 = ZIP (xs, REVERSE y0)) /\
                 (case ys1 of
                    [] => F
                  | x1::x2 =>
                      r = (x0, x1)::r1 /\ ys = x2)) ==>
          ?y0 : 'a list.
            y = APPEND y0 ys /\
            LENGTH y0 = LENGTH x /\
            r = ZIP (x, REVERSE y0)))``;
