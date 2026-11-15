(* Statement-only formalization of PutnamBench artifact putnam_1981_b4:
   real linear subspaces of 5 by 7 matrices and the existence of matrices of
   specified ranks. This file contains no proof. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Vectors.Fin Reals.

Import ListNotations.
Open Scope R_scope.

Definition putnam_1981_b4_matrix : Type :=
  Fin.t 5 -> Fin.t 7 -> R.

Definition putnam_1981_b4_linear_combination
    (r : R) (A : putnam_1981_b4_matrix)
    (s : R) (B : putnam_1981_b4_matrix) :
    putnam_1981_b4_matrix :=
  fun i j => r * A i j + s * B i j.

Fixpoint putnam_1981_b4_sum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: rest => x + putnam_1981_b4_sum rest
  end.

Definition putnam_1981_b4_delete_nth
    {T : Type} (j : nat) (xs : list T) : list T :=
  firstn j xs ++ skipn (S j) xs.

Definition putnam_1981_b4_cofactor_sign (j : nat) : R :=
  if Nat.even j then 1 else -1.

Fixpoint putnam_1981_b4_det
    (n : nat) (M : list (list R)) {struct n} : R :=
  match n with
  | O => 1
  | S k =>
      match M with
      | [] => 0
      | row :: rows =>
          putnam_1981_b4_sum
            (map
              (fun j : nat =>
                putnam_1981_b4_cofactor_sign j *
                nth j row 0 *
                putnam_1981_b4_det k
                  (map (putnam_1981_b4_delete_nth j) rows))
              (seq 0 (S k)))
      end
  end.

Definition putnam_1981_b4_minor
    (A : putnam_1981_b4_matrix)
    (rows : list (Fin.t 5))
    (cols : list (Fin.t 7)) : list (list R) :=
  map (fun i => map (fun j => A i j) cols) rows.

Definition putnam_1981_b4_rank_at_least
    (A : putnam_1981_b4_matrix) (k : nat) : Prop :=
  exists rows : list (Fin.t 5),
    exists cols : list (Fin.t 7),
      length rows = k /\
      length cols = k /\
      NoDup rows /\
      NoDup cols /\
      putnam_1981_b4_det k
        (putnam_1981_b4_minor A rows cols) <> 0.

Definition putnam_1981_b4_rank
    (A : putnam_1981_b4_matrix) (k : nat) : Prop :=
  putnam_1981_b4_rank_at_least A k /\
  forall l : nat,
    (k < l)%nat ->
    ~ putnam_1981_b4_rank_at_least A l.

Definition putnam_1981_b4_is_linear_set
    (V : putnam_1981_b4_matrix -> Prop) : Prop :=
  forall A : putnam_1981_b4_matrix,
    V A ->
    forall B : putnam_1981_b4_matrix,
      V B ->
      forall r s : R,
        V (putnam_1981_b4_linear_combination r A s B).

Definition putnam_1981_b4_solution : Prop := False.

Theorem putnam_1981_b4
    (VAB : (putnam_1981_b4_matrix -> Prop) -> Prop)
    (Vrank : (putnam_1981_b4_matrix -> Prop) -> nat -> Prop)
    (hVAB :
      forall V : putnam_1981_b4_matrix -> Prop,
        VAB V <-> putnam_1981_b4_is_linear_set V)
    (hVrank :
      forall (V : putnam_1981_b4_matrix -> Prop) (k : nat),
        Vrank V k <->
        exists A : putnam_1981_b4_matrix,
          V A /\ putnam_1981_b4_rank A k) :
  putnam_1981_b4_solution <->
  forall V : putnam_1981_b4_matrix -> Prop,
    VAB V ->
    Vrank V 0%nat ->
    Vrank V 1%nat ->
    Vrank V 2%nat ->
    Vrank V 4%nat ->
    Vrank V 5%nat ->
    Vrank V 3%nat.
Admitted.
