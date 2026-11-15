(* Statement-only formalization of Logipedia corpus artifact bigops.mk_Aop
   (catalog title bigops.mk_Aop): two-sided identity and associativity of a
   binary operation imply the abstract Aop predicate at its identity element.
   This file contains no proof. *)

Parameter Aop : forall A : Type, A -> Prop.

Theorem bigops_mk_Aop :
  forall (A : Type) (nil : A) (op : A -> A -> A),
    (forall a : A, op nil a = a) ->
    (forall a : A, op a nil = a) ->
    (forall a b c : A, op a (op b c) = op (op a b) c) ->
    Aop A nil.
Admitted.
