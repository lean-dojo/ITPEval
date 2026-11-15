(* Statement-only formalization of Logipedia corpus artifact
   bigops.eq_bigop_body_S (catalog title "bigops.eq_bigop_body_S"):
   Leibniz equality identifies the successor-index big-operation body with
   the function that conditionally combines the current value with the
   preceding aggregate. This file contains no proof. *)

Definition leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Parameter bigop bigop_body :
  forall H : Type,
    nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H.

Theorem bigops_eq_bigop_body_S :
  forall (H : Type) (n : nat),
    leibniz
      ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
      (bigop_body H (S n))
      (fun (p : nat -> bool) (nil : H)
           (op : H -> H -> H) (f : nat -> H) =>
         if p n
         then op (f n) (bigop H n p nil op f)
         else bigop H n p nil op f).
Admitted.
