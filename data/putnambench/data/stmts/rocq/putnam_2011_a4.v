(* Statement-only formalization of PutnamBench corpus artifact putnam_2011_a4:
   positive dimensions admitting an integer matrix with even row norms and
   odd dot products between distinct rows. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin ZArith.

Open Scope Z_scope.

Definition putnam_2011_a4_matrix (n : nat) : Type :=
  Fin.t n -> Fin.t n -> Z.

Fixpoint putnam_2011_a4_fin_sum
    (n : nat) : (Fin.t n -> Z) -> Z :=
  match n as m return (Fin.t m -> Z) -> Z with
  | O => fun _ => 0
  | S k =>
      fun f =>
        f Fin.F1 +
        putnam_2011_a4_fin_sum k (fun i => f (Fin.FS i))
  end.

Definition putnam_2011_a4_row_dot
    {n : nat}
    (A : putnam_2011_a4_matrix n)
    (r1 r2 : Fin.t n) : Z :=
  putnam_2011_a4_fin_sum n (fun c => A r1 c * A r2 c).

Definition putnam_2011_a4_solution (n : nat) : Prop :=
  Nat.Odd n.

Theorem putnam_2011_a4
    (nmat : nat -> Prop)
    (hnmat :
      forall n : nat,
        nmat n <->
        exists A : putnam_2011_a4_matrix n,
          (forall r : Fin.t n,
            Z.even (putnam_2011_a4_row_dot A r r) = true) /\
          (forall r1 r2 : Fin.t n,
            r1 <> r2 ->
            Z.odd (putnam_2011_a4_row_dot A r1 r2) = true))
    (n : nat)
    (npos : (0 < n)%nat) :
  nmat n <-> putnam_2011_a4_solution n.
Admitted.
