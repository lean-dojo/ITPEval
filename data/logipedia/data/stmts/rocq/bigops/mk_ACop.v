(* Statement-only formalization of Logipedia corpus artifact bigops.mk_ACop
   (catalog title bigops.mk_ACop): two-sided identity, associativity, and
   commutativity of a binary operation imply the abstract ACop predicate at
   its identity element. This file contains no proof. *)

Parameter ACop : forall A : Type, A -> Prop.

Theorem bigops_mk_ACop :
  forall (A : Type) (nil : A) (op : A -> A -> A),
    (forall a : A, op nil a = a) ->
    (forall a : A, op a nil = a) ->
    (forall a b c : A, op a (op b c) = op (op a b) c) ->
    (forall a b : A, op a b = op b a) ->
    ACop A nil.
Admitted.
