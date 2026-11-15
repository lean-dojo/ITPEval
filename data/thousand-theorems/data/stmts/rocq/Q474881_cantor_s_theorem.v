(*
  Statement-only formalization of Thousand Theorems corpus artifact Q474881
  (thousand-theorems__rocq__Q474881), "Cantor's theorem": no function from
  an arbitrary type to its powerset is surjective. This file contains no
  proof.
*)

Set Universe Polymorphism.

Theorem cantor_surjective :
  forall (A : Type) (f : A -> (A -> Prop)),
    ~ (forall S : A -> Prop, exists x : A, f x = S).
Admitted.
