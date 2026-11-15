(* Statement-only formalization of Hundred Theorems item 088,
   "Derangements Formula". This file contains no proof. *)

From Stdlib Require Import Reals List ZArith Lia Factorial.
Import ListNotations.

(* Insert x at every position of xs. *)
Fixpoint insert_everywhere (x : nat) (xs : list nat) : list (list nat) :=
  match xs with
  | [] => [[x]]
  | y :: ys =>
      (x :: y :: ys) ::
      map (fun zs => y :: zs) (insert_everywhere x ys)
  end.

(* Enumerate all permutations of a list. For [seq 0 n], every permutation
   occurs exactly once because the input entries are distinct. *)
Fixpoint permutations (xs : list nat) : list (list nat) :=
  match xs with
  | [] => [[]]
  | x :: ys =>
      flat_map (insert_everywhere x) (permutations ys)
  end.

Definition fixed_point_free (n : nat) (p : list nat) : bool :=
  forallb
    (fun i => negb (Nat.eqb (nth i p n) i))
    (seq 0 n).

Definition derangements (n : nat) : list (list nat) :=
  filter (fixed_point_free n) (permutations (seq 0 n)).

Definition derangement_count (n : nat) : nat :=
  length (derangements n).

Definition round (r : R) :=
  if Rlt_dec (R_dist r (IZR (Int_part r))) (/ INR 2)
  then Some (Int_part r)
  else if Rlt_dec (R_dist (IZR (up r)) r) (/ INR 2)
       then Some (up r)
       else None.

(* The number of derangements is the nearest integer to n! / e. *)
Theorem drm_formula :
  forall n,
    n > 0 ->
    round (INR (fact n) * exp (-1)) =
      Some (Z.of_nat (derangement_count n)).
Proof.
Admitted.
