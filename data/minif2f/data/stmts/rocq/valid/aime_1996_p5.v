From Stdlib Require Import Reals.

Open Scope R_scope.

Definition C := (R * R)%type.

Definition C_of_R (x : R) : C := (x, 0).

Definition C_add (x y : C) : C :=
  (fst x + fst y, snd x + snd y).

Definition C_neg (x : C) : C :=
  (- fst x, - snd x).

Definition C_sub (x y : C) : C :=
  C_add x (C_neg y).

Definition C_mul (x y : C) : C :=
  (fst x * fst y - snd x * snd y,
   fst x * snd y + snd x * fst y).

Fixpoint C_pow (x : C) (n : nat) : C :=
  match n with
  | O => C_of_R 1
  | S k => C_mul x (C_pow x k)
  end.

Definition first_polynomial (x : C) : C :=
  C_sub
    (C_add
      (C_add
        (C_pow x 3)
        (C_mul (C_of_R 3) (C_pow x 2)))
      (C_mul (C_of_R 4) x))
    (C_of_R 11).

Definition second_polynomial (r s t x : C) : C :=
  C_add
    (C_add
      (C_add
        (C_pow x 3)
        (C_mul r (C_pow x 2)))
      (C_mul s x))
    t.

Theorem aime_1996_p5 :
  forall (a b c r s t : C) (f g : C -> C),
  (forall x, f x = first_polynomial x) ->
  (forall x, g x = second_polynomial r s t x) ->
  f a = C_of_R 0 ->
  f b = C_of_R 0 ->
  f c = C_of_R 0 ->
  g (C_add a b) = C_of_R 0 ->
  g (C_add b c) = C_of_R 0 ->
  g (C_add c a) = C_of_R 0 ->
  a <> b ->
  b <> c ->
  c <> a ->
  t = C_of_R 23.
Proof.
Admitted.
