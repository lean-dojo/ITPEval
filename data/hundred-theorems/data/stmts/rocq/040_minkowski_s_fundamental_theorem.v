(*
  Statement-only formalization of "Minkowski's Fundamental Theorem" from
  Hundred Theorems item 040. It states Blichfeldt's lattice-point principle
  and the strict and compact forms of Minkowski's convex-body theorem for
  Lebesgue volume and the integer lattice in finite-dimensional real space.
  This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals ZArith.

Local Open Scope R_scope.

Definition euclidean_point (n : nat) : Type := Fin.t n -> R.

Definition euclidean_set (n : nat) : Type := euclidean_point n -> Prop.

Definition point_equal {n : nat}
    (x y : euclidean_point n) : Prop :=
  forall i : Fin.t n, x i = y i.

Definition point_sub {n : nat}
    (x y : euclidean_point n) : euclidean_point n :=
  fun i => x i - y i.

Definition point_neg {n : nat}
    (x : euclidean_point n) : euclidean_point n :=
  fun i => - x i.

Definition point_zero {n : nat} : euclidean_point n :=
  fun _ => 0.

Definition point_distinct {n : nat}
    (x y : euclidean_point n) : Prop :=
  ~ point_equal x y.

Definition point_nonzero {n : nat}
    (x : euclidean_point n) : Prop :=
  point_distinct x point_zero.

Definition integer_vector {n : nat}
    (x : euclidean_point n) : Prop :=
  forall i : Fin.t n, exists z : Z, x i = IZR z.

Definition convex_euclidean_set {n : nat}
    (body : euclidean_set n) : Prop :=
  forall x y : euclidean_point n,
    body x ->
    body y ->
    forall t : R,
      0 <= t <= 1 ->
      body (fun i => (1 - t) * x i + t * y i).

Definition origin_symmetric {n : nat}
    (body : euclidean_set n) : Prop :=
  forall x : euclidean_point n, body x -> body (point_neg x).

Definition euclidean_close {n : nat}
    (x y : euclidean_point n) (epsilon : R) : Prop :=
  forall i : Fin.t n, Rabs (x i - y i) < epsilon.

Definition euclidean_converges {n : nat}
    (u : nat -> euclidean_point n) (x : euclidean_point n) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall k : nat,
        (N <= k)%nat ->
        euclidean_close (u k) x epsilon.

Definition strictly_increasing (r : nat -> nat) : Prop :=
  forall i j : nat, (i < j)%nat -> (r i < r j)%nat.

Definition compact_euclidean_set {n : nat}
    (body : euclidean_set n) : Prop :=
  forall u : nat -> euclidean_point n,
    (forall k : nat, body (u k)) ->
    exists r : nat -> nat,
      strictly_increasing r /\
      exists x : euclidean_point n,
        body x /\ euclidean_converges (fun k => u (r k)) x.

Fixpoint fin_product (n : nat) : (Fin.t n -> R) -> R :=
  match n as k return (Fin.t k -> R) -> R with
  | O => fun _ => 1
  | S k =>
      fun factors =>
        factors Fin.F1 *
        fin_product k (fun i => factors (Fin.FS i))
  end.

Fixpoint partial_sum (terms : nat -> R) (count : nat) : R :=
  match count with
  | O => 0
  | S k => partial_sum terms k + terms k
  end.

(* The lower-cut relation c <= sum terms, including divergent sums as infinity. *)
Definition nonnegative_series_ge
    (terms : nat -> R) (c : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists count : nat,
      c - epsilon < partial_sum terms count.

Definition open_box {n : nat}
    (lower upper x : euclidean_point n) : Prop :=
  forall i : Fin.t n, lower i < x i /\ x i < upper i.

Definition valid_box {n : nat}
    (lower upper : euclidean_point n) : Prop :=
  forall i : Fin.t n, lower i < upper i.

Definition box_volume {n : nat}
    (lower upper : euclidean_point n) : R :=
  fin_product n (fun i => upper i - lower i).

Definition countable_open_box_cover {n : nat}
    (body : euclidean_set n)
    (lower upper : nat -> euclidean_point n) : Prop :=
  (forall k : nat, valid_box (lower k) (upper k)) /\
  forall x : euclidean_point n,
    body x ->
    exists k : nat, open_box (lower k) (upper k) x.

(*
  This is the lower Dedekind cut of Lebesgue outer volume: c belongs to
  the cut exactly when every countable open-box cover has total volume
  at least c. It represents finite values and positive infinity uniformly.
*)
Definition lebesgue_outer_volume_ge {n : nat}
    (body : euclidean_set n) (c : R) : Prop :=
  forall lower upper : nat -> euclidean_point n,
    countable_open_box_cover body lower upper ->
    nonnegative_series_ge
      (fun k => box_volume (lower k) (upper k)) c.

Definition outer_volume_sum_ge {n : nat}
    (left right : euclidean_set n) (c : R) : Prop :=
  exists a b : R,
    lebesgue_outer_volume_ge left a /\
    lebesgue_outer_volume_ge right b /\
    c <= a + b.

Definition set_intersection {n : nat}
    (left right : euclidean_set n) : euclidean_set n :=
  fun x => left x /\ right x.

Definition set_difference {n : nat}
    (left right : euclidean_set n) : euclidean_set n :=
  fun x => left x /\ ~ right x.

(* Caratheodory measurability for the concrete outer volume above. *)
Definition lebesgue_measurable {n : nat}
    (body : euclidean_set n) : Prop :=
  forall (test : euclidean_set n) (c : R),
    lebesgue_outer_volume_ge test c <->
    outer_volume_sum_ge
      (set_intersection test body)
      (set_difference test body) c.

Definition lebesgue_volume_ge {n : nat}
    (body : euclidean_set n) (c : R) : Prop :=
  lebesgue_outer_volume_ge body c.

Definition lebesgue_volume_gt {n : nat}
    (body : euclidean_set n) (c : R) : Prop :=
  exists epsilon : R,
    0 < epsilon /\
    lebesgue_outer_volume_ge body (c + epsilon).

Theorem blichfeldt_principle :
  forall (dimension_index : nat)
         (body : euclidean_set (S dimension_index)),
    lebesgue_measurable body ->
    lebesgue_volume_gt body 1 ->
    exists x y : euclidean_point (S dimension_index),
      body x /\
      body y /\
      point_distinct x y /\
      integer_vector (point_sub x y).
Admitted.

Theorem minkowski_fundamental_theorem :
  forall (dimension_index : nat)
         (body : euclidean_set (S dimension_index)),
    convex_euclidean_set body ->
    origin_symmetric body ->
    lebesgue_measurable body ->
    lebesgue_volume_gt body (2 ^ (S dimension_index)) ->
    exists x : euclidean_point (S dimension_index),
      body x /\ point_nonzero x /\ integer_vector x.
Admitted.

Theorem minkowski_compact :
  forall (dimension_index : nat)
         (body : euclidean_set (S dimension_index)),
    convex_euclidean_set body ->
    compact_euclidean_set body ->
    origin_symmetric body ->
    lebesgue_volume_ge body (2 ^ (S dimension_index)) ->
    exists x : euclidean_point (S dimension_index),
      body x /\ point_nonzero x /\ integer_vector x.
Admitted.
