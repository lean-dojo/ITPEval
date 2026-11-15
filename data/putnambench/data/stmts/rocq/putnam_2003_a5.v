(* Statement-only formalization of PutnamBench corpus artifact putnam_2003_a5:
   a one-to-one correspondence between Dyck n-paths with no even-length return
   and Dyck (n-1)-paths; this file contains no proof. *)

From Stdlib Require Import ZArith Arith.PeanoNat Vectors.Fin.

Open Scope Z_scope.

Definition putnam_2003_a5_path (m : nat) : Type :=
  Fin.t (2 * m) -> Z.

Fixpoint putnam_2003_a5_fin_sum
    (m : nat) : (Fin.t m -> Z) -> Z :=
  match m as k return (Fin.t k -> Z) -> Z with
  | O => fun _ => 0
  | S k =>
      fun p =>
        p Fin.F1 +
        putnam_2003_a5_fin_sum k (fun i => p (Fin.FS i))
  end.

Definition putnam_2003_a5_index
    {m : nat} (i : Fin.t m) : nat :=
  proj1_sig (Fin.to_nat i).

Definition putnam_2003_a5_prefix_sum
    {m : nat} (p : Fin.t m -> Z) (j : Fin.t m) : Z :=
  putnam_2003_a5_fin_sum m
    (fun k =>
      if Nat.leb (putnam_2003_a5_index k) (putnam_2003_a5_index j)
      then p k
      else 0).

Definition putnam_2003_a5_dyckpath
    (m : nat) (p : putnam_2003_a5_path m) : Prop :=
  (forall k : Fin.t (2 * m), p k = 1 \/ p k = -1) /\
  putnam_2003_a5_fin_sum (2 * m) p = 0 /\
  forall j : Fin.t (2 * m),
    0 <= putnam_2003_a5_prefix_sum p j.

Definition putnam_2003_a5_no_even_return
    (m : nat) (p : putnam_2003_a5_path m) : Prop :=
  ~ exists i j : Fin.t (2 * m),
      (putnam_2003_a5_index i < putnam_2003_a5_index j)%nat /\
      p i = 1 /\
      (forall k : Fin.t (2 * m),
        (putnam_2003_a5_index i < putnam_2003_a5_index k)%nat ->
        (putnam_2003_a5_index k <= putnam_2003_a5_index j)%nat ->
        p k = -1) /\
      Nat.Even
        (putnam_2003_a5_index j - putnam_2003_a5_index i) /\
      putnam_2003_a5_prefix_sum p j = 0.

Definition putnam_2003_a5_eligible
    (m : nat) (p : putnam_2003_a5_path m) : Prop :=
  putnam_2003_a5_dyckpath m p /\
  putnam_2003_a5_no_even_return m p.

Theorem putnam_2003_a5
    (n : nat)
    (npos : (0 < n)%nat) :
  exists f :
      putnam_2003_a5_path n ->
      putnam_2003_a5_path (n - 1),
    forall y : putnam_2003_a5_path (n - 1),
      putnam_2003_a5_dyckpath (n - 1) y ->
      exists! x : putnam_2003_a5_path n,
        putnam_2003_a5_eligible n x /\ f x = y.
Admitted.
