(* Statement-only formalization of Euler's evaluation of the Basel series. *)

needs "Library/transc.ml";;

let EULER_HARMONIC_SUM =
  `(\m. inv (&(m + 1) pow 2)) sums (pi pow 2 / &6)`;;
