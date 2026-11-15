(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binary_sqrt_BinarySqrt_sqrt_mainqtvc: a binary-square-root
  verification condition preserving nonnegativity of the radicand and
  positivity of the error tolerance, together with unit arithmetic
  identities. This file contains no proof.
*)

let statement =
  `!r eps:real.
     &0 <= r
     ==> &0 < eps
     ==> &0 <= r /\
         &0 < eps /\
         (&1:int) <= (&1:int) /\
         eps = (&1:real) * eps`;;
