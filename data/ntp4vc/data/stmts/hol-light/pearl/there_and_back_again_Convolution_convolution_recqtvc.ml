(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/there_and_back_again_Convolution_convolution_recqtvc: the recursive
  symbolic-convolution verification condition, relating the consumed prefix
  of the second list to its reversal paired elementwise with the first list
  and returning the unconsumed suffix. This file contains no proof.
*)

let statement =
 `!x y:A list.
    LENGTH x <= LENGTH y
    ==>
    (if x = [] then
       T
     else
       let x0 = HD x in
       let xs = TL x in
       ((if x = [] then F else TL x = xs) /\
        LENGTH xs <= LENGTH y) /\
       (!o1:(A#A)list.
        !o2:A list.
          (?y0:A list.
             y = APPEND y0 o2 /\
             LENGTH y0 = LENGTH xs /\
             o1 = ZIP xs (REVERSE y0))
          ==>
          (if o2 = [] then F else T))) /\
    (!r:(A#A)list.
     !ys:A list.
       (if x = [] then
          r = [] /\ ys = y
        else
          let x0 = HD x in
          let xs = TL x in
          ?r1:(A#A)list.
          ?ys1:A list.
            (?y0:A list.
               y = APPEND y0 ys1 /\
               LENGTH y0 = LENGTH xs /\
               r1 = ZIP xs (REVERSE y0)) /\
            (if ys1 = [] then
               F
             else
               r = CONS (x0,HD ys1) r1 /\
               ys = TL ys1))
       ==>
       (?y0:A list.
          y = APPEND y0 ys /\
          LENGTH y0 = LENGTH x /\
          r = ZIP x (REVERSE y0)))`;;
