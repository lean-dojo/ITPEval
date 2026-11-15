(* Statement-only formalization of PutnamBench corpus artifact putnam_2009_b2:
   the attainable total costs of finite strictly rightward jumps from zero to
   one with cost b^3 - a*b^2 are exactly the reals in (1/3, 1]; this file
   contains no proof. *)

From Stdlib Require Import Reals Arith.PeanoNat.

Open Scope R_scope.

Fixpoint putnam_2009_b2_total_cost
    (s : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k =>
      putnam_2009_b2_total_cost s k +
      ((s (S k)) ^ 3 - s k * (s (S k)) ^ 2)
  end.

Definition putnam_2009_b2_strict_mono
    (s : nat -> R) : Prop :=
  forall i j : nat, (i < j)%nat -> s i < s j.

Definition putnam_2009_b2_attainable
    (c : R) : Prop :=
  exists s : nat -> R,
    s O = 0 /\
    putnam_2009_b2_strict_mono s /\
    exists n : nat,
      s n = 1 /\
      putnam_2009_b2_total_cost s n = c.

Theorem putnam_2009_b2 :
  forall c : R,
    putnam_2009_b2_attainable c <->
    1 / 3 < c <= 1.
Admitted.
