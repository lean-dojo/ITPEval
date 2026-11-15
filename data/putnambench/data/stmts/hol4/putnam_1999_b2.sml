(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b2:
  a complex polynomial satisfying P(x) = Q(x) P''(x) for a quadratic Q has
  degree-many distinct roots if it has two distinct roots. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory complexTheory monoidTheory ringTheory;
open polynomialTheory polyDerivativeTheory;

val putnam_1999_b2 =
  ``let cr : complex ring =
      <| carrier := UNIV;
         sum := <| carrier := UNIV; id := 0; op := complex_add |>;
         prod := <| carrier := UNIV; id := 1; op := complex_mul |> |>
    in
      !P Q : complex poly.
        Poly cr P /\
        Poly cr Q /\
        poly_deg cr Q = 2 /\
        (!x : complex.
           poly_eval cr P x =
             poly_eval cr Q x *
             poly_eval cr (poly_diff cr (poly_diff cr P)) x)
        ==>
        ((?x1 x2 : complex.
            x1 <> x2 /\
            poly_eval cr P x1 = 0 /\
            poly_eval cr P x2 = 0)
         ==>
         ?f : num -> complex.
           INJ f (count (poly_deg cr P)) UNIV /\
           !i : num.
             i < poly_deg cr P
             ==>
             poly_eval cr P (f i) = 0)``;
