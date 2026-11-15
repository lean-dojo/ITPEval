(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a3:
  the greatest universal lower bound for the average modulus of the roots of
  a degree-2019 polynomial with real coefficients
  1 <= b_0 < ... < b_2019 <= 2019 is 2019^(-1/2019).
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory transcTheory complexTheory;

val putnam_2019_a3 =
  ``let polynomial =
      \b : num -> real.
      \z : complex.
        ITSET
          (\k acc. complex_of_real (b k) * z pow k + acc)
          (count 2020)
          (0 : complex)
    in
    let admissible =
      \b : num -> real.
        1 <= b 0 /\
        b 2019 <= 2019 /\
        (!i : num. i < 2019 ==> b i < b (SUC i)) /\
        (!i : num. 2019 < i ==> b i = 0)
    in
    let full_root_list =
      \b : num -> real.
      \roots : complex list.
        LENGTH roots = 2019 /\
        !z : complex.
          polynomial b z =
            complex_of_real (b 2019) *
            FOLDL
              (\acc root. acc * (z - root))
              (1 : complex)
              roots
    in
    let root_average =
      \roots : complex list.
        SUM (MAP modu roots) / 2019
    in
    let lower_bound =
      \M : real.
        !b : num -> real. !roots : complex list.
          admissible b /\ full_root_list b roots
          ==>
          M <= root_average roots
    in
    let solution =
      (2019 : real) powr (-(1 : real) / 2019)
    in
      lower_bound solution /\
      !M : real. lower_bound M ==> M <= solution``;
