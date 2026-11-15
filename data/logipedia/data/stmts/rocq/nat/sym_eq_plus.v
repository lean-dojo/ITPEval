(*
  Statement-only formalization of Logipedia corpus artifact nat.sym_eq_plus
  (catalog title "nat.sym_eq_plus"): for every natural input, the filtered
  natural addition body is Leibniz-equal to the partially applied addition
  function. This file contains no proof.
*)

Definition logipedia_leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Definition logipedia_filter_nat_type
    (return_type : Type)
    (return_ : nat -> return_type)
    (n : nat) : return_type :=
  return_ n.

Fixpoint logipedia_plus (n m : nat) : nat :=
  match n with
  | O => m
  | S k => S (logipedia_plus k m)
  end.

Definition logipedia_plus_body : nat -> nat -> nat :=
  logipedia_plus.

Theorem logipedia_nat_sym_eq_plus :
  forall n : nat,
    logipedia_leibniz
      (nat -> nat)
      (logipedia_filter_nat_type
        (nat -> nat) logipedia_plus_body n)
      (logipedia_plus n).
Admitted.
