(* Statement-only formalization of Logipedia corpus artifact bigops.timesA
   (catalog title bigops.timesA): the source module's opaque Aop predicate
   holds for the successor of zero in the natural-number domain. This file
   contains no proof. *)

Parameter Aop : forall A : Type, A -> Prop.

Theorem bigops_timesA :
  Aop nat (S O).
Admitted.
