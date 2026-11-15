(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527217 (thousand-theorems__hol4__Q3527217), "M. Riesz extension theorem":
  a real-linear functional on a subspace that is nonnegative on a generating
  cone extends to a global real-linear functional nonnegative on that cone.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val q3527217_real_vector_space_def = new_definition (
  "q3527217_real_vector_space_def",
  ``q3527217_real_vector_space
      (zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y))``);

val q3527217_subspace_def = new_definition (
  "q3527217_subspace_def",
  ``q3527217_subspace
      (zero : 'v) (add : 'v -> 'v -> 'v)
      (smul : real -> 'v -> 'v) (domain : 'v -> bool) <=>
      domain zero /\
      (!x y. domain x /\ domain y ==> domain (add x y)) /\
      (!a x. domain x ==> domain (smul a x))``);

val q3527217_pointed_cone_def = new_definition (
  "q3527217_pointed_cone_def",
  ``q3527217_pointed_cone
      (zero : 'v) (add : 'v -> 'v -> 'v)
      (smul : real -> 'v -> 'v) (cone : 'v -> bool) <=>
      cone zero /\
      (!x y. cone x /\ cone y ==> cone (add x y)) /\
      (!a x. 0 <= a /\ cone x ==> cone (smul a x))``);

val q3527217_linear_on_def = new_definition (
  "q3527217_linear_on_def",
  ``q3527217_linear_on
      (add : 'v -> 'v -> 'v) (smul : real -> 'v -> 'v)
      (domain : 'v -> bool) (f : 'v -> real) <=>
      (!x y.
        domain x /\ domain y ==>
        f (add x y) = f x + f y) /\
      (!a x.
        domain x ==>
        f (smul a x) = a * f x)``);

val q3527217_linear_def = new_definition (
  "q3527217_linear_def",
  ``q3527217_linear
      (add : 'v -> 'v -> 'v) (smul : real -> 'v -> 'v)
      (g : 'v -> real) <=>
      (!x y. g (add x y) = g x + g y) /\
      (!a x. g (smul a x) = a * g x)``);

val riesz_extension =
  ``!(zero : 'v) (add : 'v -> 'v -> 'v) (neg : 'v -> 'v)
      (smul : real -> 'v -> 'v)
      (domain : 'v -> bool) (cone : 'v -> bool)
      (f : 'v -> real).
      q3527217_real_vector_space zero add neg smul /\
      q3527217_subspace zero add smul domain /\
      q3527217_pointed_cone zero add smul cone /\
      q3527217_linear_on add smul domain f /\
      (!x. domain x /\ cone x ==> 0 <= f x) /\
      (!y. ?x. domain x /\ cone (add x y))
      ==>
      ?g : 'v -> real.
        q3527217_linear add smul g /\
        (!x. domain x ==> g x = f x) /\
        !x. cone x ==> 0 <= g x``;
