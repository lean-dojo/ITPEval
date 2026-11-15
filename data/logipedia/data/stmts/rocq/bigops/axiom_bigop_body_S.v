(* Statement-only formalization of Logipedia corpus artifact
   bigops.axiom_bigop_body_S: the successor equation for a polymorphic
   filtered big-operation body, conditionally combining the current value
   with the preceding aggregate. This file contains no proof. *)

Parameter connectives_equal : forall A : Type, A -> A -> Prop.

Parameter bigop bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_axiom_bigop_body_S :
  forall (H : Type) (n : nat),
    connectives_equal
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (bigop_body H (S n))
      (fun (p : nat -> bool) (nil : H)
           (op : H -> H -> H) (f : nat -> H) =>
         if p n
         then op (f n) (bigop H n p nil op f)
         else bigop H n p nil op f).
Admitted.
