(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binary_sqrt_BinarySqrt_sqrt_mainqtvc: a binary square-root routine's
  entry verification condition for a nonnegative radicand and positive error
  tolerance, including the resulting unit arithmetic obligations. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val sqrt_main_vc =
  ``!r eps : real.
      0 <= r ==>
      0 < eps ==>
      0 <= r /\
      0 < eps /\
      (1 : int) <= 1 /\
      eps = real_of_int (1 : int) * eps``;
