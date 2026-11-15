(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1566341
  (thousand-theorems__rocq__Q1566341), "Hindman's theorem": every finite
  cover of the finite-product set of an infinite stream in a semigroup has a
  member containing the finite-product set of another infinite stream. This
  file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q1566341_stream (M : Type) : Type := nat -> M.

Definition q1566341_stream_tail
    {M : Type} (a : q1566341_stream M) : q1566341_stream M :=
  fun n => a (S n).

Inductive q1566341_FP
    {M : Type}
    (mul : M -> M -> M) :
    q1566341_stream M -> M -> Prop :=
| q1566341_FP_head :
    forall a : q1566341_stream M,
      q1566341_FP mul a (a 0)
| q1566341_FP_tail :
    forall (a : q1566341_stream M) (m : M),
      q1566341_FP mul (q1566341_stream_tail a) m ->
      q1566341_FP mul a m
| q1566341_FP_cons :
    forall (a : q1566341_stream M) (m : M),
      q1566341_FP mul (q1566341_stream_tail a) m ->
      q1566341_FP mul a (mul (a 0) m).

Definition q1566341_set_equiv
    {M : Type} (c d : M -> Prop) : Prop :=
  forall x : M, c x <-> d x.

Definition q1566341_finite
    {M : Type} (s : (M -> Prop) -> Prop) : Prop :=
  exists members : list (M -> Prop),
    forall c : M -> Prop,
      s c <->
      exists d : M -> Prop,
        In d members /\ q1566341_set_equiv c d.

Theorem q1566341_FP_partition_regular :
  forall (M : Type)
         (mul : M -> M -> M),
    (forall x y z : M,
      mul (mul x y) z = mul x (mul y z)) ->
    forall (a : q1566341_stream M)
           (s : (M -> Prop) -> Prop),
      q1566341_finite s ->
      (forall m : M,
        q1566341_FP mul a m ->
        exists c : M -> Prop, s c /\ c m) ->
      exists c : M -> Prop,
        s c /\
        exists b : q1566341_stream M,
          forall m : M, q1566341_FP mul b m -> c m.
Admitted.
