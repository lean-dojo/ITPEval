(* Statement-only formalization of PutnamBench artifact putnam_1986_a5:
   functions on a positive-dimensional real coordinate space whose
   cross-partial differences are constant admit a scalar adjustment making
   every component linear; this file contains no proof. *)

From Stdlib Require Import
  Vectors.Fin
  Reals
  ClassicalDescription
  ClassicalEpsilon.

Open Scope R_scope.

Definition putnam_1986_a5_vector (n : nat) : Type :=
  Fin.t n -> R.

Fixpoint putnam_1986_a5_fin_sum
    (n : nat) : (Fin.t n -> R) -> R :=
  match n as k return (Fin.t k -> R) -> R with
  | O => fun _ => 0
  | S k =>
      fun u =>
        u Fin.F1 +
        putnam_1986_a5_fin_sum k (fun i => u (Fin.FS i))
  end.

Definition putnam_1986_a5_distance {n : nat}
    (x y : putnam_1986_a5_vector n) : R :=
  sqrt
    (putnam_1986_a5_fin_sum n
      (fun i : Fin.t n => (x i - y i) ^ 2)).

Definition putnam_1986_a5_replace {n : nat}
    (x : putnam_1986_a5_vector n)
    (i : Fin.t n) (xi : R) : putnam_1986_a5_vector n :=
  fun j : Fin.t n =>
    if Fin.eq_dec j i then xi else x j.

Definition putnam_1986_a5_real_derivative
    (u : R -> R) (x : R) : R :=
  match excluded_middle_informative
          (exists d : R, derivable_pt_lim u x d) with
  | left _ =>
      epsilon (inhabits 0)
        (fun d : R => derivable_pt_lim u x d)
  | right _ => 0
  end.

Definition putnam_1986_a5_partial_derivative {n : nat}
    (u : putnam_1986_a5_vector n -> R)
  (i : Fin.t n) : putnam_1986_a5_vector n -> R :=
  fun x =>
    putnam_1986_a5_real_derivative
      (fun xi : R => u (putnam_1986_a5_replace x i xi))
      (x i).

Definition putnam_1986_a5_continuous {n : nat}
    (u : putnam_1986_a5_vector n -> R) : Prop :=
  forall x : putnam_1986_a5_vector n,
    forall eps : R,
      eps > 0 ->
      exists delta : R,
        delta > 0 /\
        forall y : putnam_1986_a5_vector n,
          putnam_1986_a5_distance y x < delta ->
          Rabs (u y - u x) < eps.

Definition putnam_1986_a5_twice_continuously_differentiable {n : nat}
  (u : putnam_1986_a5_vector n -> R) : Prop :=
  (forall (i : Fin.t n) (x : putnam_1986_a5_vector n),
      derivable_pt_lim
        (fun xi : R => u (putnam_1986_a5_replace x i xi))
        (x i)
        (putnam_1986_a5_partial_derivative u i x)) /\
  (forall (i j : Fin.t n) (x : putnam_1986_a5_vector n),
      derivable_pt_lim
        (fun xj : R =>
          putnam_1986_a5_partial_derivative u i
            (putnam_1986_a5_replace x j xj))
        (x j)
        (putnam_1986_a5_partial_derivative
          (putnam_1986_a5_partial_derivative u i) j x)) /\
  (forall i j : Fin.t n,
      putnam_1986_a5_continuous
        (putnam_1986_a5_partial_derivative
          (putnam_1986_a5_partial_derivative u i) j)).

Definition putnam_1986_a5_linear {n : nat}
    (u : putnam_1986_a5_vector n -> R) : Prop :=
  (forall x y : putnam_1986_a5_vector n,
      u (fun i : Fin.t n => x i + y i) = u x + u y) /\
  (forall (a : R) (x : putnam_1986_a5_vector n),
      u (fun i : Fin.t n => a * x i) = a * u x).

Theorem putnam_1986_a5
    (n : nat)
    (hn : (1 <= n)%nat)
    (f : Fin.t n -> putnam_1986_a5_vector n -> R)
    (hf :
      forall i : Fin.t n,
        putnam_1986_a5_twice_continuously_differentiable (f i))
    (C : Fin.t n -> Fin.t n -> R)
    (hf' :
      forall (i j : Fin.t n) (x : putnam_1986_a5_vector n),
        putnam_1986_a5_partial_derivative (f i) j x -
        putnam_1986_a5_partial_derivative (f j) i x =
        C i j) :
  exists g : putnam_1986_a5_vector n -> R,
    forall i : Fin.t n,
      putnam_1986_a5_linear
        (fun x : putnam_1986_a5_vector n =>
          f i x + putnam_1986_a5_partial_derivative g i x).
Admitted.
