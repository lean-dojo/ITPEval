(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_minus_body_S (catalog title "nat.sym_eq_minus_body_S"): for every
  natural number, Leibniz equality relates the natural-number matcher with its
  successor at zero and the preceding subtraction at successors to the
  natural-subtraction body at that successor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Definition logipedia_match_nat_type
    (return_type : Type)
    (case_O : return_type)
    (case_S : nat -> return_type)
    (z : nat) : return_type :=
  match z with
  | O => case_O
  | S n => case_S n
  end.

Definition logipedia_minus (n m : nat) : nat :=
  Nat.sub n m.

Definition logipedia_minus_body (n : nat) : nat -> nat :=
  match n with
  | O => fun _ : nat => O
  | S p =>
      fun m : nat =>
        logipedia_match_nat_type
          nat (S p) (fun q : nat => logipedia_minus p q) m
  end.

Theorem logipedia_nat_sym_eq_minus_body_S :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (fun m : nat =>
         logipedia_match_nat_type
           nat (S n) (fun q : nat => logipedia_minus n q) m)
      (logipedia_minus_body (S n)).
Admitted.
