(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b4:
  the vector space of real bivariate polynomials of total degree at most 2009
  whose average on every origin-centered circle is zero has dimension 2020050.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pairTheory pred_setTheory realTheory;
open real_sigmaTheory transcTheory integrationTheory;

val putnam_2009_b4 =
  ``let support =
      \P : num # num -> real.
        {ij : num # num | P ij <> 0}
    in
    let eval =
      \P : num # num -> real.
      \x y : real.
        REAL_SUM_IMAGE
          (\ij : num # num.
             P ij * x pow (FST ij) * y pow (SND ij))
          (support P)
    in
    let degree_at_most =
      \n : num.
      \P : num # num -> real.
        !i j : num. n < i + j ==> P (i, j) = 0
    in
    let balanced =
      \P : num # num -> real.
        !r : real.
          0 < r
          ==>
          integration$integral (interval [0, 2 * pi])
            (\t : real. eval P (r * cos t) (r * sin t)) /
            (2 * pi * r) =
          0
    in
    let V =
      {P : num # num -> real |
         degree_at_most 2009 P /\ balanced P}
    in
    let vzero =
      (\ij : num # num. (0 : real))
    in
    let vadd =
      \(P : num # num -> real) (Q : num # num -> real).
        \ij : num # num. P ij + Q ij
    in
    let smul =
      \(c : real) (P : num # num -> real).
        \ij : num # num. c * P ij
    in
    let lincomb =
      \(m : num) (coeff : num -> real)
       (vec : num -> (num # num -> real)).
        FOLDL
          (\acc i. vadd acc (smul (coeff i) (vec i)))
          vzero
          (GENLIST (\i. i) m)
    in
    let independent =
      \basis : (num # num -> real) list.
        !coeff : num -> real.
          lincomb (LENGTH basis) coeff (\i. EL i basis) = vzero
          ==>
          !i : num. i < LENGTH basis ==> coeff i = 0
    in
    let has_dimension =
      \W : (num # num -> real) set.
      \d : num.
        ?basis : (num # num -> real) list.
          LENGTH basis = d /\
          ALL_DISTINCT basis /\
          (!i : num. i < d ==> EL i basis IN W) /\
          independent basis /\
          (!P : num # num -> real.
             P IN W
             ==>
             ?coeff : num -> real.
               lincomb d coeff (\i. EL i basis) = P)
    in
      has_dimension V 2020050``;
