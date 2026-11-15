(* Statement-only formalization of Logipedia corpus artifact
   bigops.bigop_Sfalse: a filtered big operation at a successor index
   ignores the current value when its Boolean predicate is false. This file
   contains no proof. *)

From Stdlib Require Import Bool.Bool.

Fixpoint bigop {B : Type}
    (n : nat) (p : nat -> bool) (nil : B)
    (op : B -> B -> B) (f : nat -> B) : B :=
  match n with
  | O => nil
  | S k =>
      if p k
      then op (f k) (bigop k p nil op f)
      else bigop k p nil op f
  end.

Theorem bigops_bigop_Sfalse :
  forall (B : Type) (k : nat) (p : nat -> bool)
         (nil : B) (op : B -> B -> B) (f : nat -> B),
    p k = false ->
    bigop (S k) (fun i => p i) nil op (fun i => f i) =
    bigop k (fun i => p i) nil op (fun i => f i).
Admitted.
