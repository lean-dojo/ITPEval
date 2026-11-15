From mathcomp Require Import all_algebra all_ssreflect.
From mathcomp Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Definition putnam_2017_a2_ratfun := ({poly rat} * {poly rat})%type.

Definition putnam_2017_a2_valid (q : putnam_2017_a2_ratfun) : Prop :=
  q.2 != 0.

Definition putnam_2017_a2_eq
    (q r : putnam_2017_a2_ratfun) : Prop :=
  q.1 * r.2 = r.1 * q.2.

Definition putnam_2017_a2_mul
    (q r : putnam_2017_a2_ratfun) : putnam_2017_a2_ratfun :=
  (q.1 * r.1, q.2 * r.2).

Definition putnam_2017_a2_sub
    (q r : putnam_2017_a2_ratfun) : putnam_2017_a2_ratfun :=
  (q.1 * r.2 - r.1 * q.2, q.2 * r.2).

Definition putnam_2017_a2_one : putnam_2017_a2_ratfun :=
  ((1%Z%:Q)%:P, (1%Z%:Q)%:P).

Definition putnam_2017_a2_X : putnam_2017_a2_ratfun :=
  ('X, (1%Z%:Q)%:P).

Theorem putnam_2017_a2
    (Q : nat -> putnam_2017_a2_ratfun)
    (hQvalid : forall n, putnam_2017_a2_valid (Q n))
    (hQbase :
      putnam_2017_a2_eq (Q 0%nat) putnam_2017_a2_one /\
      putnam_2017_a2_eq (Q 1%nat) putnam_2017_a2_X)
    (hQn : forall n : nat,
      putnam_2017_a2_eq
        (putnam_2017_a2_mul (Q (n.+2)) (Q n))
        (putnam_2017_a2_sub
          (putnam_2017_a2_mul (Q (n.+1)) (Q (n.+1)))
          putnam_2017_a2_one))
    (n : nat)
    (hn : lt 0 n) :
    exists P : {poly int},
      putnam_2017_a2_eq
        (Q n)
        ((map_poly intr P : {poly rat}), (1%Z%:Q)%:P).
Proof. Admitted.
