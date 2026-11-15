(*
  Statement-only formalization of miniF2F valid problem
  algebra_2complexrootspoly_xsqp49eqxp7itxpn7i: the factorization of x squared plus 49 over
  the complex numbers using the imaginary unit. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val algebra_2complexrootspoly_xsqp49eqxp7itxpn7i =
  ``!x : complex.
      x pow 2 + 49 = (x + 7 * i) * (x - 7 * i)``;
