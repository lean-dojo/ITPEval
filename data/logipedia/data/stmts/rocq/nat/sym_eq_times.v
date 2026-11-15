(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_times
  (catalog title "nat.sym_eq_times"): for every natural number, the filtered
  multiplication body is Leibniz-equal to the corresponding multiplication
  function. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter filter_nat_type :
  forall return_type : Type,
    (nat -> return_type) -> nat -> return_type.
Parameters times_body times : nat -> nat -> nat.

Theorem logipedia_nat_sym_eq_times :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (filter_nat_type (nat -> nat) times_body n)
      (times n).
Admitted.
