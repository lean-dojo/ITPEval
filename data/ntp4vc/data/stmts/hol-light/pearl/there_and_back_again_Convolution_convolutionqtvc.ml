(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/there_and_back_again_Convolution_convolutionqtvc: the top-level
  symbolic-convolution verification condition for equal-length lists,
  identifying the complete reversed second list paired elementwise with the
  first list. This file contains no proof.
*)

let statement =
 `!x y:A list.
    LENGTH x = LENGTH y
    ==>
    LENGTH x <= LENGTH y /\
    (!o1:(A#A)list.
     !o2:A list.
       (?y0:A list.
          y = APPEND y0 o2 /\
          LENGTH y0 = LENGTH x /\
          o1 = ZIP x (REVERSE y0))
       ==>
       o1 = ZIP x (REVERSE y))`;;
