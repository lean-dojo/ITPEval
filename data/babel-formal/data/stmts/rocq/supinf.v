Class CompleteOrderedField := {
  R         : Type;
  NatAlt    : Type;
  zero_nat  : NatAlt;
  Succ      : NatAlt -> NatAlt;
  NatAltle  : NatAlt -> NatAlt -> Prop;

  zero      : R;
  one       : R;
  add       : R -> R -> R;
  mul       : R -> R -> R;
  opp       : R -> R;
  inv       : R -> R;
  Rle       : R -> R -> Prop;
  Rlt       : R -> R -> Prop;
  Rabs      : R -> R;
  INR       : NatAlt -> R;

  le_succ_of_le : forall n m, NatAltle n m -> NatAltle n (Succ m);
  le_succ       : forall n, NatAltle n (Succ n);
  NatAltle_n : forall n : NatAlt, NatAltle n n;

  add_comm      : forall x y, add x y = add y x;
  add_assoc     : forall x y z, add (add x y) z = add x (add y z);
  add_zero      : forall x, add x zero = x;
  add_opp       : forall x, add (opp x) x = zero;
  mul_comm      : forall x y, mul x y = mul y x;
  mul_assoc     : forall x y z, mul (mul x y) z = mul x (mul y z);
  mul_one       : forall x, mul x one = x;
  dist_l        : forall x y z, mul x (add y z) = add (mul x y) (mul x z);
  sub_zero      : forall x, add x (opp zero) = x;

  Rle_refl      : forall x, Rle x x;
  Rle_trans     : forall x y z, Rle x y -> Rle y z -> Rle x z;
  Rle_antisym   : forall x y, Rle x y -> Rle y x -> x = y;
  Rlt_def       : forall x y, Rlt x y <-> (Rle x y /\ x <> y);
  Rle_abs       : forall x, Rle (add x (opp zero)) (Rabs x);
  Rinv_0_lt_compat   : forall x, Rlt zero x -> Rlt zero (inv x);
  Rplus_le_compat_l  : forall x y z, Rle y z -> Rle (add x y) (add x z);
  Rinv_involutive    : forall x, Rlt zero x -> inv (inv x) = x;

  INR_pos       : forall n, Rlt zero (INR (Succ n));
  INR_le        : forall m n, NatAltle m n -> Rle (INR m) (INR n);
  INR_0         : INR zero_nat = zero;
  INR_S         : forall n, INR (Succ n) = add (INR n) one;

  Rtotal_order       : forall x y, Rlt x y \/ x = y \/ Rlt y x;
  Rle_inv_contravar  : forall a b, Rlt zero a -> Rlt zero b -> Rle a b -> Rle (inv b) (inv a);
  eps_between        : forall x y, Rlt x y -> exists eps, Rlt zero eps /\ Rlt (add x eps) y;

  archimedean  : forall x, exists n, Rle x (INR n);
  completeness  : forall A : R -> Prop,
    (exists ub, forall a, A a -> Rle ub a) ->
    exists sup,
      (forall a, A a -> Rle a sup) /\
      (forall y, (forall a, A a -> Rle a y) -> Rle sup y)
}.

Section SupInf.
  Context {F : CompleteOrderedField}.

  Infix "+"   := add.
  Infix "*"   := mul.
  Notation "- x" := (opp x).
  Notation "x - y" := (add x (opp y)).
  Notation "/ x" := (inv x).
  Infix "<="   := NatAltle (at level 70).

  Infix "<=R"   := Rle (at level 70).
  Infix "<R"    := Rlt (at level 70).
  Infix ">R"    := (fun x y => Rlt y x) (at level 70).
  Notation "| x |" := (Rabs x) (at level 40).

  Definition up_bounds (A : R -> Prop) (x : R) : Prop :=
    forall a, A a -> Rle a x.
  
  Definition is_maximum (a : R) (A : R -> Prop) : Prop :=
    A a /\ up_bounds A a.
  Infix "is_a_max_of" := is_maximum (at level 70).
  Lemma add_sub_cancel_r : forall a b : R,
  a + (b - a) = b.
Proof.
Admitted.
  Print add_sub_cancel_r.
  Lemma Rabs_pos (t : R) : t <=R |t|.
Proof.
Admitted.
  Print Rabs_pos.
  
  Lemma unique_max (A : R -> Prop) (x y : R) :
    x is_a_max_of A -> y is_a_max_of A -> x = y.
Proof.
Admitted.
  
  Definition low_bounds (A : R -> Prop) : R -> Prop :=
    fun x => forall a, A a -> x <=R a.

  Definition is_inf (x : R) (A : R -> Prop) : Prop :=
    is_maximum x (low_bounds A).
  Infix "is_an_inf_of" := is_inf (at level 70).
  
  Axiom classic : forall P:Prop, P \/ ~P.
  Lemma inf_lt (A : R -> Prop) (x : R) :
    x is_an_inf_of A -> forall y, x <R y -> exists a, A a /\ a <R y.
Proof.
Admitted.

  Lemma le_of_le_add_eps (x y : R) :
    (forall eps, eps >R zero -> y <=R x + eps) -> y <=R x.
Proof.
Admitted.
  
  Definition limit (u : NatAlt -> R) (l : R) : Prop :=
    forall eps, eps >R zero -> exists N, forall n : NatAlt, (N <= n) -> |u n - l| <=R eps.

  Lemma le_lim (x y : R) (u : NatAlt -> R) :
  limit u x -> (forall n : NatAlt, y <=R u n) -> y <=R x.
Proof.
Admitted.

  Lemma inv_succ_pos : forall n, zero <R / INR (Succ n).
Proof.
Admitted.

  Lemma limit_inv_succ : forall eps : R, eps >R zero ->
    exists N, forall n : NatAlt, (N <= n) -> / INR (Succ n) <=R eps.
Proof.
Admitted.


End SupInf.
