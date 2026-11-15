(*
  Statement-only formalization of Thousand Theorems corpus artifact Q282649
  (thousand-theorems__rocq__Q282649), "Pentagonal number theorem": over an
  arbitrary commutative ring with an arbitrary topology, the infinite product
  of the formal power series 1 - X^(n + 1) converges in the coefficientwise
  topology to the signed series supported on generalized pentagonal numbers.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q282649_commutative_ring (R : Type) : Type := {
  q282649_zero : R;
  q282649_one : R;
  q282649_add : R -> R -> R;
  q282649_mul : R -> R -> R;
  q282649_neg : R -> R;
  q282649_add_assoc :
    forall x y z : R,
      q282649_add x (q282649_add y z) =
      q282649_add (q282649_add x y) z;
  q282649_add_comm :
    forall x y : R,
      q282649_add x y = q282649_add y x;
  q282649_add_zero :
    forall x : R,
      q282649_add x q282649_zero = x;
  q282649_add_neg :
    forall x : R,
      q282649_add x (q282649_neg x) = q282649_zero;
  q282649_mul_assoc :
    forall x y z : R,
      q282649_mul x (q282649_mul y z) =
      q282649_mul (q282649_mul x y) z;
  q282649_mul_comm :
    forall x y : R,
      q282649_mul x y = q282649_mul y x;
  q282649_mul_one :
    forall x : R,
      q282649_mul x q282649_one = x;
  q282649_left_distrib :
    forall x y z : R,
      q282649_mul x (q282649_add y z) =
      q282649_add
        (q282649_mul x y) (q282649_mul x z)
}.

Arguments q282649_zero {R} _.
Arguments q282649_one {R} _.
Arguments q282649_add {R} _ _ _.
Arguments q282649_mul {R} _ _ _.
Arguments q282649_neg {R} _ _.

Definition q282649_set (A : Type) : Type := A -> Prop.

Definition q282649_same_set {A : Type}
    (U V : q282649_set A) : Prop :=
  forall x : A, U x <-> V x.

Record q282649_topological_space (A : Type) : Type := {
  q282649_is_open : q282649_set A -> Prop;
  q282649_open_extensional :
    forall U V : q282649_set A,
      q282649_same_set U V ->
      (q282649_is_open U <-> q282649_is_open V);
  q282649_open_empty :
    q282649_is_open (fun _ : A => False);
  q282649_open_full :
    q282649_is_open (fun _ : A => True);
  q282649_open_intersection :
    forall U V : q282649_set A,
      q282649_is_open U ->
      q282649_is_open V ->
      q282649_is_open (fun x : A => U x /\ V x);
  q282649_open_union :
    forall family : q282649_set A -> Prop,
      (forall U : q282649_set A,
        family U -> q282649_is_open U) ->
      q282649_is_open
        (fun x : A =>
          exists U : q282649_set A,
            family U /\ U x)
}.

Arguments q282649_is_open {A} _ _.

Definition q282649_power_series (R : Type) : Type := nat -> R.

Definition q282649_ps_one {R : Type}
    (CR : q282649_commutative_ring R) : q282649_power_series R :=
  fun n : nat =>
    match n with
    | O => q282649_one CR
    | S _ => q282649_zero CR
    end.

Definition q282649_ps_neg {R : Type}
    (CR : q282649_commutative_ring R)
    (a : q282649_power_series R) : q282649_power_series R :=
  fun n : nat => q282649_neg CR (a n).

Definition q282649_ps_add {R : Type}
    (CR : q282649_commutative_ring R)
    (a b : q282649_power_series R) : q282649_power_series R :=
  fun n : nat => q282649_add CR (a n) (b n).

Definition q282649_ps_sub {R : Type}
    (CR : q282649_commutative_ring R)
    (a b : q282649_power_series R) : q282649_power_series R :=
  q282649_ps_add CR a (q282649_ps_neg CR b).

Fixpoint q282649_convolution_sum {R : Type}
    (CR : q282649_commutative_ring R)
    (a b : q282649_power_series R)
    (total count : nat) : R :=
  match count with
  | O => q282649_mul CR (a O) (b total)
  | S count' =>
      q282649_add CR
        (q282649_convolution_sum CR a b total count')
        (q282649_mul CR
          (a (S count')) (b (Nat.sub total (S count'))))
  end.

Definition q282649_ps_mul {R : Type}
    (CR : q282649_commutative_ring R)
    (a b : q282649_power_series R) : q282649_power_series R :=
  fun n : nat => q282649_convolution_sum CR a b n n.

Definition q282649_X {R : Type}
    (CR : q282649_commutative_ring R) : q282649_power_series R :=
  fun n : nat =>
    if Nat.eqb n 1 then q282649_one CR else q282649_zero CR.

Fixpoint q282649_ps_pow {R : Type}
    (CR : q282649_commutative_ring R)
    (a : q282649_power_series R)
    (n : nat) : q282649_power_series R :=
  match n with
  | O => q282649_ps_one CR
  | S k => q282649_ps_mul CR a (q282649_ps_pow CR a k)
  end.

Definition q282649_one_sub_X_pow {R : Type}
    (CR : q282649_commutative_ring R)
    (n : nat) : q282649_power_series R :=
  q282649_ps_sub CR
    (q282649_ps_one CR)
    (q282649_ps_pow CR (q282649_X CR) (S n)).

Definition q282649_pentagonal (k : Z) : nat :=
  Z.to_nat (Z.div (k * (3 * k - 1)) 2).

Definition q282649_pentagonal_lower (m : nat) : nat :=
  Nat.div (m * (3 * m - 1)) 2.

Definition q282649_pentagonal_upper (m : nat) : nat :=
  Nat.div (m * (3 * m + 1)) 2.

Fixpoint q282649_neg_one_pow_nat {R : Type}
    (CR : q282649_commutative_ring R)
    (m : nat) : R :=
  match m with
  | O => q282649_one CR
  | S k =>
      q282649_mul CR
        (q282649_neg CR (q282649_one CR))
        (q282649_neg_one_pow_nat CR k)
  end.

Fixpoint q282649_pentagonal_coefficient_search {R : Type}
    (CR : q282649_commutative_ring R)
    (n fuel m : nat) : R :=
  match fuel with
  | O => q282649_zero CR
  | S fuel' =>
      if orb
          (Nat.eqb n (q282649_pentagonal_lower m))
          (Nat.eqb n (q282649_pentagonal_upper m))
      then q282649_neg_one_pow_nat CR m
      else q282649_pentagonal_coefficient_search CR n fuel' (S m)
  end.

Definition q282649_pentagonal_series {R : Type}
    (CR : q282649_commutative_ring R) : q282649_power_series R :=
  fun n : nat =>
    q282649_pentagonal_coefficient_search CR n (S (S n)) O.

Record q282649_finset (A : Type) : Type := {
  q282649_elements : list A;
  q282649_elements_nodup : NoDup q282649_elements
}.

Arguments q282649_elements {A} _.

Definition q282649_finset_subset {A : Type}
    (s t : q282649_finset A) : Prop :=
  forall x : A,
    In x (q282649_elements s) ->
    In x (q282649_elements t).

Fixpoint q282649_finite_product_list {R : Type}
    (CR : q282649_commutative_ring R)
    (f : nat -> q282649_power_series R)
    (indices : list nat) : q282649_power_series R :=
  match indices with
  | nil => q282649_ps_one CR
  | cons n rest =>
      q282649_ps_mul CR
        (f n) (q282649_finite_product_list CR f rest)
  end.

Definition q282649_finite_product {R : Type}
    (CR : q282649_commutative_ring R)
    (f : nat -> q282649_power_series R)
    (s : q282649_finset nat) : q282649_power_series R :=
  q282649_finite_product_list CR f (q282649_elements s).

Definition q282649_power_series_net_converges {R : Type}
    (T : q282649_topological_space R)
    (net : q282649_finset nat -> q282649_power_series R)
    (limit : q282649_power_series R) : Prop :=
  forall (coefficient : nat) (U : q282649_set R),
    q282649_is_open T U ->
    U (limit coefficient) ->
    exists base : q282649_finset nat,
      forall stage : q282649_finset nat,
        q282649_finset_subset base stage ->
        U (net stage coefficient).

Definition q282649_has_prod {R : Type}
    (CR : q282649_commutative_ring R)
    (T : q282649_topological_space R)
    (f : nat -> q282649_power_series R)
    (limit : q282649_power_series R) : Prop :=
  q282649_power_series_net_converges T
    (fun s : q282649_finset nat =>
      q282649_finite_product CR f s)
    limit.

Module PowerSeries.
Module WithPiTopology.

Theorem hasProd_one_sub_X_pow :
  forall (R : Type)
         (CR : q282649_commutative_ring R)
         (T : q282649_topological_space R),
    q282649_has_prod CR T
      (q282649_one_sub_X_pow CR)
      (q282649_pentagonal_series CR).
Admitted.

End WithPiTopology.
End PowerSeries.
