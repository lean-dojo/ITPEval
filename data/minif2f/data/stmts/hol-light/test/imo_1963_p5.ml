(*
  Statement-only formalization of miniF2F test artifact imo_1963_p5: a
  trigonometric identity for cosines at the angles pi/7, 2*pi/7, and 3*pi/7.
  This file contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `cos (pi / &7) - cos (&2 * pi / &7) + cos (&3 * pi / &7) =
   &1 / &2`;;
