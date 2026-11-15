(* Statement-only formalization of PutnamBench artifact putnam_2000_b3:
   multiplicity-weighted zero counts of successive derivatives of a real
   trigonometric polynomial are nondecreasing and tend to twice its highest
   frequency. This file contains no proof. *)

From Stdlib Require Import
  Reals Lists.List Arith.PeanoNat
  ClassicalDescription ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_2000_b3_total_derivative
    (f : R -> R) (x : R) : R :=
  match excluded_middle_informative
          (exists d : R, derivable_pt_lim f x d) with
  | left _ =>
      epsilon (inhabits (0 : R))
        (fun d : R => derivable_pt_lim f x d)
  | right _ => 0
  end.

Fixpoint putnam_2000_b3_iterated_derivative
    (n : nat) (f : R -> R) : R -> R :=
  match n with
  | O => f
  | S k =>
      putnam_2000_b3_total_derivative
        (putnam_2000_b3_iterated_derivative k f)
  end.

Definition putnam_2000_b3_trigonometric_sum
    (N : nat) (a : nat -> R) (t : R) : R :=
  fold_right Rplus 0
    (map
      (fun j : nat =>
        a j * sin (2 * PI * INR j * t))
      (seq 1 N)).

Definition putnam_2000_b3_weighted_zero_count
    (mult : (R -> R) -> R -> nat)
    (g : R -> R)
    (total : nat) : Prop :=
  exists zeros : list R,
    NoDup zeros /\
    (forall t : R,
      In t zeros <->
        0 <= t /\ t < 1 /\ mult g t <> O) /\
    total =
      fold_right Nat.add O (map (mult g) zeros).

Theorem putnam_2000_b3
    (N : nat)
    (a : nat -> R)
    (f : R -> R)
    (mult : (R -> R) -> R -> nat)
    (M : nat -> nat)
    (Npos : (O < N)%nat)
    (haN : a N <> 0)
    (hf : forall t : R,
      f t = putnam_2000_b3_trigonometric_sum N a t)
    (hmult : forall (g : R -> R) (t : R),
      (exists c : nat,
        putnam_2000_b3_iterated_derivative c g t <> 0) ->
      putnam_2000_b3_iterated_derivative (mult g t) g t <> 0 /\
      forall k : nat,
        (k < mult g t)%nat ->
        putnam_2000_b3_iterated_derivative k g t = 0)
    (hM : forall k : nat,
      putnam_2000_b3_weighted_zero_count
        mult (putnam_2000_b3_iterated_derivative k f) (M k)) :
  (forall i j : nat,
    (i <= j)%nat ->
    (M i <= M j)%nat) /\
  exists K : nat,
    forall k : nat,
      (K <= k)%nat ->
      M k = (2 * N)%nat.
Admitted.
