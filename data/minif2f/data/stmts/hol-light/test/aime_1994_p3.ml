(*
  Statement-only formalization of miniF2F test problem aime_1994_p3:
  the integer recurrence holds at every index. This file contains no proof.
*)

let statement =
  `!f:int->int.
     (!x:int. f x + f (x - &1) = x pow 2) /\
     f (&19) = &94
     ==> ((f (&94) == &561) (mod &1000))`;;
