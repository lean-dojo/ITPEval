(* Statement-only formalization of PutnamBench artifact putnam_1968_b6:
   no sequence of compact sets of rational numbers contains every compact
   set of rational numbers as a subset. This file contains no proof. *)

From Stdlib Require Import QArith Qabs List.

Open Scope Q_scope.

Definition qset : Type := Q -> Prop.

Definition q_subset (S T : qset) : Prop :=
  forall x : Q, S x -> T x.

Definition q_open (U : qset) : Prop :=
  forall x : Q,
    U x ->
    exists epsilon : Q,
      0 < epsilon /\
      forall y : Q, Qabs (y - x) < epsilon -> U y.

Definition q_open_cover (cover : qset -> Prop) (S : qset) : Prop :=
  (forall U : qset, cover U -> q_open U) /\
  (forall x : Q, S x -> exists U : qset, cover U /\ U x).

Definition q_compact (S : qset) : Prop :=
  forall cover : qset -> Prop,
    q_open_cover cover S ->
    exists finite_cover : list qset,
      (forall U : qset, List.In U finite_cover -> cover U) /\
      (forall x : Q,
        S x ->
        exists U : qset, List.In U finite_cover /\ U x).

Theorem putnam_1968_b6 :
  ~ exists K : nat -> qset,
      (forall n : nat, q_compact (K n)) /\
      (forall S : qset,
        q_compact S ->
        exists n : nat, q_subset S (K n)).
Proof. Admitted.
