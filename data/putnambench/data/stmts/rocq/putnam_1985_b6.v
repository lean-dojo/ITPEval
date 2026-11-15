(* Statement-only formalization of PutnamBench artifact putnam_1985_b6:
   a finite group of real square matrices whose traces sum to zero has matrix
   sum equal to the zero matrix. This file contains no proof. *)

From Stdlib Require Import Lists.List Vectors.Fin Reals.

Import ListNotations.
Open Scope R_scope.

Definition putnam_1985_b6_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> R.

Definition putnam_1985_b6_matrix_eq {n : nat}
    (A B : putnam_1985_b6_matrix n) : Prop :=
  forall i j : Fin.t n, A i j = B i j.

Fixpoint putnam_1985_b6_fin_sum
    (n : nat) : (Fin.t n -> R) -> R :=
  match n as k return (Fin.t k -> R) -> R with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_1985_b6_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_1985_b6_matrix_zero
    (n : nat) : putnam_1985_b6_matrix n :=
  fun _ _ => 0.

Definition putnam_1985_b6_matrix_identity
    (n : nat) : putnam_1985_b6_matrix n :=
  fun i j => if Fin.eq_dec i j then 1 else 0.

Definition putnam_1985_b6_matrix_add {n : nat}
    (A B : putnam_1985_b6_matrix n) : putnam_1985_b6_matrix n :=
  fun i j => A i j + B i j.

Definition putnam_1985_b6_matrix_mul {n : nat}
    (A B : putnam_1985_b6_matrix n) : putnam_1985_b6_matrix n :=
  fun i j =>
    putnam_1985_b6_fin_sum n (fun k => A i k * B k j).

Definition putnam_1985_b6_trace {n : nat}
    (A : putnam_1985_b6_matrix n) : R :=
  putnam_1985_b6_fin_sum n (fun i => A i i).

Fixpoint putnam_1985_b6_matrix_sum {n : nat}
    (G : list (putnam_1985_b6_matrix n)) : putnam_1985_b6_matrix n :=
  match G with
  | [] => putnam_1985_b6_matrix_zero n
  | A :: rest =>
      putnam_1985_b6_matrix_add A
        (putnam_1985_b6_matrix_sum rest)
  end.

Fixpoint putnam_1985_b6_trace_sum {n : nat}
    (G : list (putnam_1985_b6_matrix n)) : R :=
  match G with
  | [] => 0
  | A :: rest =>
      putnam_1985_b6_trace A + putnam_1985_b6_trace_sum rest
  end.

Definition putnam_1985_b6_member {n : nat}
    (A : putnam_1985_b6_matrix n)
    (G : list (putnam_1985_b6_matrix n)) : Prop :=
  exists B : putnam_1985_b6_matrix n,
    In B G /\ putnam_1985_b6_matrix_eq A B.

Fixpoint putnam_1985_b6_nodup {n : nat}
    (G : list (putnam_1985_b6_matrix n)) : Prop :=
  match G with
  | [] => True
  | A :: rest =>
      ~ putnam_1985_b6_member A rest /\
      putnam_1985_b6_nodup rest
  end.

Theorem putnam_1985_b6
    (n : nat)
    (npos : (0 < n)%nat)
    (G : list (putnam_1985_b6_matrix n))
    (Gnodup : putnam_1985_b6_nodup G)
    (groupG :
      (forall g h : putnam_1985_b6_matrix n,
        putnam_1985_b6_member g G ->
        putnam_1985_b6_member h G ->
        putnam_1985_b6_member (putnam_1985_b6_matrix_mul g h) G) /\
      putnam_1985_b6_member (putnam_1985_b6_matrix_identity n) G /\
      (forall g : putnam_1985_b6_matrix n,
        putnam_1985_b6_member g G ->
        exists h : putnam_1985_b6_matrix n,
          putnam_1985_b6_member h G /\
          putnam_1985_b6_matrix_eq
            (putnam_1985_b6_matrix_mul g h)
            (putnam_1985_b6_matrix_identity n)))
    (hG : putnam_1985_b6_trace_sum G = 0) :
  putnam_1985_b6_matrix_eq
    (putnam_1985_b6_matrix_sum G)
    (putnam_1985_b6_matrix_zero n).
Admitted.
