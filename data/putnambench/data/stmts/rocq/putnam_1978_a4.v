(* Statement-only formalization of PutnamBench artifact putnam_1978_a4:
   consequences of the binary-operation identity (ab)(cd) = ad and the
   existence of a finite operation satisfying three additional conditions.
   This file contains no proof. *)

From Stdlib Require Import Lists.List.

Definition putnam_1978_a4_finite_type (S : Type) : Prop :=
  exists enumeration : list S,
    forall x : S, List.In x enumeration.

Definition putnam_1978_a4_bypass
    {S : Type}
    (op : S -> S -> S) : Prop :=
  forall a b c d : S,
    op (op a b) (op c d) = op a d.

Theorem putnam_1978_a4 :
  (forall (S : Type) (op : S -> S -> S),
      putnam_1978_a4_bypass op ->
      forall a b c : S,
        op a b = c ->
        op c c = c /\
        forall d : S, op a d = op c d) /\
  (exists (S : Type) (op : S -> S -> S),
      putnam_1978_a4_finite_type S /\
      putnam_1978_a4_bypass op /\
      (forall a : S, op a a = a) /\
      (exists a b : S, op a b = a /\ a <> b) /\
      (exists a b : S, op a b <> a)).
Admitted.
