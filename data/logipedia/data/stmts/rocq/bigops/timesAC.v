(* Statement-only formalization of Logipedia corpus artifact bigops.timesAC
   (catalog title bigops.timesAC): the source module's abstract ACop predicate
   holds for the successor of zero in the natural-number domain. This file
   contains no proof. *)

Parameter ACop : forall A : Type, A -> Prop.

Theorem bigops_timesAC :
  ACop nat (S O).
Admitted.
