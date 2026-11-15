(* Statement-only formalization of Logipedia corpus artifact
   bigops.axiom_bigop_body_O: the polymorphic connectives.equal relation
   identifies the zero-index big-operation body with the constant function
   returning its nil element. This file contains no proof. *)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.

Parameter bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_axiom_bigop_body_O :
  forall H : Type,
    connectives_equal
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (bigop_body H 0)
      (fun (_ : nat -> bool) (nil : H)
           (_ : H -> H -> H) (_ : nat -> H) => nil).
Admitted.
