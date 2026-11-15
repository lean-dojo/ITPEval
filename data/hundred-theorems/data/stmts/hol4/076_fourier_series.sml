(*
  Statement-only formalization of the Hundred Theorems artifact 076,
  "Fourier Series". It states that every real square-integrable function on
  [-pi, pi] is the L2 limit of its normalized trigonometric Fourier partial
  sums. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory iterateTheory realTheory transcTheory;
open topologyTheory real_topologyTheory extrealTheory measureTheory borelTheory;
open lebesgueTheory lebesgue_measureTheory;

val fourier_series_l2 =
  ``let domain = interval [(-pi : real), pi] in
    let trigonometric_set =
      \i x.
        if i = 0 then
          1 / sqrt (2 * pi)
        else if ODD i then
          sin ((&(i DIV 2 + 1) : real) * x) / sqrt pi
        else
          cos ((&(i DIV 2) : real) * x) / sqrt pi
    in
    let fourier_coefficient =
      \f i.
        real
          (integral lebesgue
            (\x. Normal (trigonometric_set i x * f x) *
                 indicator_fn domain x))
    in
    let l2norm =
      \g.
        sqrt
          (real
            (integral lebesgue
              (\x. Normal ((g x) pow 2) * indicator_fn domain x)))
    in
      !f : real -> real.
        (\x. Normal (f x) * indicator_fn domain x) IN
          measurable (m_space lebesgue, measurable_sets lebesgue) Borel /\
        integrable lebesgue
          (\x. Normal ((f x) pow 2) * indicator_fn domain x)
        ==>
        (((\n.
             l2norm
               (\x.
                  f x -
                  SIGMA
                    (\i. fourier_coefficient f i *
                         trigonometric_set i x)
                    (count (SUC n)))) -->
          (0 : real)) sequentially)``;
