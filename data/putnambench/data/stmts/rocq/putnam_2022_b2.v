Require Import Ensembles Finite_sets Reals.
Open Scope R_scope.

Definition vect3 := (R * R * R)%type.

Definition cross_prod (v w : vect3) : vect3 :=
  let '(v1, v2, v3) := v in
  let '(w1, w2, w3) := w in
  (v2 * w3 - v3 * w2,
   v3 * w1 - v1 * w3,
   v1 * w2 - v2 * w1).

Definition putnam_2022_b2_solution : Ensemble nat :=
  fun n => n = 1%nat \/ n = 7%nat.
Theorem putnam_2022_b2
    (p : nat -> Prop := fun n =>
      exists A : Ensemble vect3,
        cardinal vect3 A n /\
        A = fun u =>
          exists v w : vect3,
            In _ A v /\
            In _ A w /\
            u = cross_prod v w)
    : forall (n: nat), ((n > 0)%nat /\ p n) <-> In _ putnam_2022_b2_solution n.
Proof. Admitted.
