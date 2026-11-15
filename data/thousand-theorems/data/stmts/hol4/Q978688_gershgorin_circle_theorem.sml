(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q978688, "Gershgorin circle theorem": every eigenvalue of a square matrix
  over an arbitrary normed field and finite index set lies in a closed ball
  centered at some diagonal entry, with radius the sum of the norms of the
  other entries in that row. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory pred_setTheory;

val q978688_normed_field_def = new_definition (
  "q978688_normed_field_def",
  ``q978688_normed_field
      (zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (invA : 'a -> 'a)
      (norm : 'a -> real) <=>
      zero <> oneA /\
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      (!x y. mul x y = mul y x) /\
      (!x y z. mul (mul x y) z = mul x (mul y z)) /\
      (!x. mul x oneA = x) /\
      (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
      invA zero = zero /\
      (!x. x <> zero ==> mul x (invA x) = oneA) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!x y. norm (mul x y) = norm x * norm y)``);

val q978688_field_sum_def = new_definition (
  "q978688_field_sum_def",
  ``q978688_field_sum
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (s : 'i set) (f : 'i -> 'a) =
      ITSET (\i acc. add (f i) acc) s zero``);

val q978688_real_sum_def = new_definition (
  "q978688_real_sum_def",
  ``q978688_real_sum (s : 'i set) (f : 'i -> real) =
      ITSET (\i acc. f i + acc) s 0``);

val q978688_has_eigenvalue_def = new_definition (
  "q978688_has_eigenvalue_def",
  ``q978688_has_eigenvalue
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (mul : 'a -> 'a -> 'a)
      (s : 'i set) (A : 'i -> 'i -> 'a) (mu : 'a) <=>
      ?v : 'i -> 'a.
        (?j : 'i. j IN s /\ v j <> zero) /\
        !i : 'i.
          i IN s ==>
          q978688_field_sum zero add s
            (\j. mul (A i j) (v j)) =
          mul mu (v i)``);

val eigenvalue_mem_ball =
  ``!(zero : 'a) (oneA : 'a)
      (add : 'a -> 'a -> 'a) (mul : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (invA : 'a -> 'a)
      (norm : 'a -> real)
      (s : 'i set) (A : 'i -> 'i -> 'a) (mu : 'a).
      q978688_normed_field zero oneA add mul neg invA norm /\
      FINITE s /\
      q978688_has_eigenvalue zero add mul s A mu
      ==>
      ?k : 'i.
        k IN s /\
        norm (add mu (neg (A k k))) <=
        q978688_real_sum (s DELETE k) (\j. norm (A k j))``;
