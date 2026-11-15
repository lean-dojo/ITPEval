(* Statement-only formalization of Thousand Theorems corpus artifact Q5171652
   (thousand-theorems__rocq__Q5171652), "Corners theorem": every sufficiently
   dense finite subset of an initial square of natural numbers contains a
   nontrivial corner once the side length meets the explicit bound. This file
   contains no proof. *)

From Stdlib Require Import Reals Lists.List Arith.PeanoNat ZArith.

Open Scope R_scope.

Record q5171652_finset (X : Type) : Type := {
  q5171652_elements : list X;
  q5171652_elements_nodup : NoDup q5171652_elements
}.

Arguments q5171652_elements {X} _.

Definition q5171652_nat_floor (x : R) : nat :=
  Z.to_nat (Int_part x).

Definition q5171652_nat_ceil (x : R) : nat :=
  Z.to_nat (Z.opp (Int_part (- x))).

Fixpoint q5171652_iterate
    {X : Type} (f : X -> X) (k : nat) (x : X) : X :=
  match k with
  | O => x
  | S k' => q5171652_iterate f k' (f x)
  end.

Definition q5171652_step_bound (n : nat) : nat :=
  (n * Nat.pow 4 n)%nat.

Definition q5171652_initial_bound (epsilon : R) (l : nat) : nat :=
  Nat.max 7
    (Nat.max l
      (S (q5171652_nat_floor
        (ln (100 / epsilon ^ 5) / ln 4)))).

Definition q5171652_regularity_bound (epsilon : R) (l : nat) : nat :=
  let t :=
    q5171652_iterate q5171652_step_bound
      (q5171652_nat_floor (4 / epsilon ^ 5))
      (q5171652_initial_bound epsilon l) in
  (t * Nat.pow 16 t)%nat.

Definition q5171652_triangle_removal_bound (epsilon : R) : R :=
  let c := q5171652_nat_ceil (4 / epsilon) in
  Rmin
    (/ (2 * INR (Nat.pow c 3)))
    ((1 - Rmin 1 epsilon / 4) *
      (epsilon /
        (16 * INR (q5171652_regularity_bound (epsilon / 8) c))) ^ 3).

Definition q5171652_corners_theorem_bound (epsilon : R) : nat :=
  S (q5171652_nat_floor
    (/ (q5171652_triangle_removal_bound (epsilon / 9) * 27))).

Definition q5171652_mem
    {X : Type} (x : X) (A : q5171652_finset X) : Prop :=
  In x (q5171652_elements A).

Definition q5171652_is_corner_free
    (A : q5171652_finset (nat * nat)) : Prop :=
  forall x1 y1 x2 y2 : nat,
    q5171652_mem (x1, y1) A ->
    q5171652_mem (x1, y2) A ->
    q5171652_mem (x2, y1) A ->
    (x1 + y2 = x2 + y1)%nat ->
    x1 = x2.

Theorem corners_theorem_nat :
  forall (epsilon : R) (n : nat),
    0 < epsilon ->
    (q5171652_corners_theorem_bound (epsilon / 9) <= n)%nat ->
    forall A : q5171652_finset (nat * nat),
      (forall p : nat * nat,
        q5171652_mem p A ->
        ((fst p < n)%nat /\ (snd p < n)%nat)) ->
      epsilon * INR (Nat.pow n 2) <=
        INR (length (q5171652_elements A)) ->
      ~ q5171652_is_corner_free A.
Admitted.
