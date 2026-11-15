(* Statement-only formalization of PutnamBench artifact putnam_1974_b4: separately continuous real functions on the plane are pointwise limits of sequences of jointly continuous functions; this file contains no proof. *)
From Stdlib Require Import Reals.

Open Scope R_scope.

Definition continuous_real (h : R -> R) : Prop :=
  forall x eps : R,
    eps > 0 ->
    exists delta : R,
      delta > 0 /\
      forall x' : R,
        Rabs (x' - x) < delta ->
        Rabs (h x' - h x) < eps.

Definition continuous_plane (h : (R * R)%type -> R) : Prop :=
  forall x y eps : R,
    eps > 0 ->
    exists delta : R,
      delta > 0 /\
      forall x' y' : R,
        Rabs (x' - x) < delta ->
        Rabs (y' - y) < delta ->
        Rabs (h (x', y') - h (x, y)) < eps.

Definition converges_pointwise_at
    (u : nat -> R) (l : R) : Prop :=
  forall eps : R,
    eps > 0 ->
    exists N : nat,
      forall n : nat,
        (n >= N)%nat ->
        Rabs (u n - l) < eps.

Theorem putnam_1974_b4
    (f : (R * R)%type -> R)
    (hfcontx :
      forall y : R, continuous_real (fun x : R => f (x, y)))
    (hfconty :
      forall x : R, continuous_real (fun y : R => f (x, y))) :
  exists g : nat -> ((R * R)%type -> R),
    (forall n : nat, continuous_plane (g n)) /\
    (forall x y : R,
      converges_pointwise_at
        (fun n : nat => g n (x, y))
        (f (x, y))).
Admitted.
