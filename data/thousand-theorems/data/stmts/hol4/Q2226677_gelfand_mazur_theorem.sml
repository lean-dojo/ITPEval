(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2226677, "Gelfand–Mazur theorem": the scalar embedding of the complex
  numbers into a complete complex normed division algebra is an algebra
  isomorphism. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory complexTheory;

val q2226677_normed_ring_def = new_definition (
  "q2226677_normed_ring_def",
  ``q2226677_normed_ring
      (zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (norm : 'a -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul oneA x = x) /\
      (!x. mul x oneA = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      (!x y z. mul (add x y) z = add (mul x z) (mul y z)) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!x y. norm (mul x y) <= norm x * norm y)``);

val q2226677_complex_normed_algebra_def = new_definition (
  "q2226677_complex_normed_algebra_def",
  ``q2226677_complex_normed_algebra
      (zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (norm : 'a -> real)
      (algebraMap : complex -> 'a) <=>
      algebraMap 0 = zero /\
      algebraMap 1 = oneA /\
      (!z w. algebraMap (z + w) = add (algebraMap z) (algebraMap w)) /\
      (!z w. algebraMap (z * w) = mul (algebraMap z) (algebraMap w)) /\
      (!z. algebraMap (-z) = neg (algebraMap z)) /\
      (!z x. mul (algebraMap z) x = mul x (algebraMap z)) /\
      (!z x. norm (mul (algebraMap z) x) <= modu z * norm x)``);

val q2226677_tendsto_def = new_definition (
  "q2226677_tendsto_def",
  ``q2226677_tendsto
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) (x : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q2226677_cauchy_def = new_definition (
  "q2226677_cauchy_def",
  ``q2226677_cauchy
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q2226677_complete_space_def = new_definition (
  "q2226677_complete_space_def",
  ``q2226677_complete_space
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) <=>
      !u : num -> 'a.
        q2226677_cauchy add neg norm u ==>
        ?x : 'a. q2226677_tendsto add neg norm u x``);

val q2226677_is_unit_def = new_definition (
  "q2226677_is_unit_def",
  ``q2226677_is_unit
      (oneA : 'a) (mul : 'a -> 'a -> 'a) (a : 'a) <=>
      ?b : 'a. mul a b = oneA /\ mul b a = oneA``);

val NormedRing_algEquivComplexOfComplete =
  ``!(zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (norm : 'a -> real)
      (algebraMap : complex -> 'a).
      q2226677_normed_ring zero oneA add mul neg norm /\
      q2226677_complex_normed_algebra
        zero oneA add mul neg norm algebraMap /\
      q2226677_complete_space add neg norm /\
      (!a : 'a.
        q2226677_is_unit oneA mul a <=> a <> zero)
      ==>
      ?inverse : 'a -> complex.
        (!z : complex. inverse (algebraMap z) = z) /\
        (!a : 'a. algebraMap (inverse a) = a)``;
