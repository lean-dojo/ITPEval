Require Import Coq.Init.Logic.

Class CRing := {
  R     : Type;
  zero  : R;
  one   : R;
  add   : R -> R -> R;
  mul   : R -> R -> R;
  opp   : R -> R;

  add_comm  : forall x y, add x y = add y x;
  add_assoc : forall x y z, add (add x y) z = add x (add y z);
  add_zero  : forall x, add x zero = x;
  zero_add  : forall x, add zero x = x;
  add_opp   : forall x, add x (opp x) = zero;

  mul_comm  : forall x y, mul x y = mul y x;
  mul_assoc : forall x y z, mul (mul x y) z = mul x (mul y z);
  mul_one   : forall x, mul x one = x;
  dist_l    : forall a x y, mul a (add x y) = add (mul a x) (mul a y);
  opp_add   : forall x y, opp (add x y) = add (opp x) (opp y)
}.

Section Ideals.
  Context {K : CRing}.

  Infix "+R" := add (at level 65).
  Infix "*R" := mul (at level 70).
  Notation "-R x" := (opp x) (at level 100).

  Record IsIdeal (I : R -> Prop) : Prop := {
    ideal_zero : I zero;
    ideal_add  : forall x y, I x -> I y -> I (x +R y);
    ideal_opp  : forall x, I x -> I (-R x);
    ideal_mul  : forall a x, I x -> I (a *R x)
  }.

  Definition Inter {I : Type} (F : I -> R -> Prop) : R -> Prop :=
    fun x => forall i, F i x.

  Lemma inter_isIdeal {I : Type} (F : I -> R -> Prop)
    (h : forall i, IsIdeal (F i)) : IsIdeal (Inter F).
Proof.
Admitted.

  Definition sum (I J : R -> Prop) : R -> Prop :=
    fun x => exists a b, I a /\ J b /\ (a +R b) = x.

  Lemma sum_isIdeal (I J : R -> Prop)
    (hI : IsIdeal I) (hJ : IsIdeal J) : IsIdeal (sum I J).
Proof.
Admitted.

End Ideals.
