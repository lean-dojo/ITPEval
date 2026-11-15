Require Import QArith.

Open Scope Q_scope.

Definition putnam_2001_b4_in_domain (x : Q) : Prop :=
  ~ (Qeq x (-1) \/ Qeq x 0 \/ Qeq x 1).

Definition putnam_2001_b4_image (f : Q -> Q) (y : Q) : Prop :=
  exists x : Q,
    putnam_2001_b4_in_domain x /\
    Qeq (f x) y.

Fixpoint putnam_2001_b4_compose_n (f : Q -> Q) (n : nat) : Q -> Q :=
  match n with
  | O => fun x => x
  | S n' => fun x => f (putnam_2001_b4_compose_n f n' x)
  end.

Definition putnam_2001_b4_solution : Prop := True.

Theorem putnam_2001_b4
    (f : Q -> Q := fun x => x - 1 / x) :
  (~ exists x : Q,
      putnam_2001_b4_in_domain x /\
      forall n : nat,
        (n >= 1)%nat ->
        putnam_2001_b4_image (putnam_2001_b4_compose_n f n) x) <->
  putnam_2001_b4_solution.
Proof. Admitted.
