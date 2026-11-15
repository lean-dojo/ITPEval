(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a3:
  among the four improper integrals of x^k divided by the specified
  reciprocal-symmetric degree-six polynomial, the minimum occurs at k = 2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory measureTheory;
open lebesgueTheory lebesgue_measureTheory;

val putnam_1978_a3 =
  ``let polynomial_value =
      \x : real.
        2 * (x pow 6 + 1) +
        4 * (x pow 5 + x) +
        3 * (x pow 4 + x pow 2) +
        5 * x pow 3
    in
    let nonnegative_reals = {x : real | 0 <= x}
    in
    let I =
      \k : num.
        let halfline = restrict_space lebesgue nonnegative_reals
        in
        let integrand =
          \x : real. Normal (x pow k / polynomial_value x)
        in
          if lebesgue$integrable halfline integrand then
            real (lebesgue$integral halfline integrand)
          else
            0
    in
      1 <= (2 : num) /\ 2 <= 4 /\
      !k : num. 1 <= k /\ k <= 4 ==> I 2 <= I k``;
