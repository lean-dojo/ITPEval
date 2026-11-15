(*
  Statement-only formalization of miniF2F valid artifact
  algebra_sqineq_2at2pclta2c2p41pc: a universal quadratic inequality over two real variables.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val algebra_sqineq_2at2pclta2c2p41pc =
  ``!a c : real.
      2 * a * (2 + c) <= a pow 2 + c pow 2 + 4 * (1 + c)``;
