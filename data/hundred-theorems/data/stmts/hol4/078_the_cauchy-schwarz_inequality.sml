(*
  Statement-only formalization of Hundred Theorems artifact
  078_the_cauchy-schwarz_inequality, cataloged as "The Cauchy-Schwarz
  Inequality": in any real inner product space, the absolute value of the
  inner product of two vectors is at most the product of their norms. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val cauchy_schwarz_inequality =
  ``let is_real_inner_product_space =
      \(zero : 'a)
       (add : 'a -> 'a -> 'a)
       (neg : 'a -> 'a)
       (smul : real -> 'a -> 'a)
       (inner : 'a -> 'a -> real).
        (!x y z. add (add x y) z = add x (add y z)) /\
        (!x y. add x y = add y x) /\
        (!x. add zero x = x) /\
        (!x. add (neg x) x = zero) /\
        (!x. smul 1 x = x) /\
        (!a b x. smul (a * b) x = smul a (smul b x)) /\
        (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
        (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
        (!x y. inner x y = inner y x) /\
        (!x y z. inner (add x y) z = inner x z + inner y z) /\
        (!a x y. inner (smul a x) y = a * inner x y) /\
        (!x. 0 <= inner x x) /\
        (!x. (inner x x = 0) <=> (x = zero))
    in
      !(zero : 'a)
       (add : 'a -> 'a -> 'a)
       (neg : 'a -> 'a)
       (smul : real -> 'a -> 'a)
       (inner : 'a -> 'a -> real).
        is_real_inner_product_space zero add neg smul inner ==>
        !u v.
          abs (inner u v) <= sqrt (inner u u) * sqrt (inner v v)``;
