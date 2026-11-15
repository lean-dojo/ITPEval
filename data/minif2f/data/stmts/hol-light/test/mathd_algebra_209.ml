(*
  Statement-only formalization of miniF2F test problem mathd_algebra_209. This file contains no
  proof.
*)

let statement =
  `!f f_inv:real->real.
    (!x:real. f (f_inv x) = x) /\
    (!x:real. f_inv (f x) = x) /\
    f_inv (&2) = &10 /\
    f_inv (&10) = &1 /\
    f_inv (&1) = &2
    ==> f (f (&10)) = &1`;;
