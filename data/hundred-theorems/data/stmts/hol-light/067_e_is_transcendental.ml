(*
  Statement-only formalization of "e is Transcendental" from Hundred Theorems
  artifact 067 (hundred-theorems__hol-light__067). It states that Euler's
  number, the real exponential of one, is transcendental. This file contains
  no proof.
*)

needs "100/liouville.ml";;

let HUNDRED_THEOREMS_067_E_IS_TRANSCENDENTAL =
  `transcendental (exp (&1))`;;
