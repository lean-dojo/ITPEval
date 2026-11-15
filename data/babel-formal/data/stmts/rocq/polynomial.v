Inductive mynat : Type :=
| O : mynat
| S : mynat -> mynat.

Fixpoint mynat_add (n m : mynat) : mynat :=
  match n with
  | O    => m
  | S n' => S (mynat_add n' m)
  end.

Inductive mynat_le : mynat -> mynat -> Prop :=
| le_n : forall n,            mynat_le n n
| le_S : forall n m, mynat_le n m -> mynat_le n (S m).

Lemma mynat_zero_le (n : mynat) : mynat_le O n.
Proof.
Admitted.

Lemma mynat_add_zero_r : forall n, mynat_add n O = n.
Proof.
Admitted.

Lemma mynat_succ_le_succ (n m : mynat) :
  mynat_le n m -> mynat_le (S n) (S m).
Proof.
Admitted.

Lemma mynat_add_S_r : forall m n,
  mynat_add m (S n) = S (mynat_add m n).
Proof.
Admitted.

Lemma mynat_add_comm : forall n m, mynat_add n m = mynat_add m n.
Proof.
Admitted.

Inductive mylist (A : Type) : Type :=
| nilL  : mylist A
| consL : A -> mylist A -> mylist A.

Arguments nilL  {A}.
Arguments consL {A} _ _.
Infix "::L" := consL (at level 60, right associativity).

Inductive InL {A : Type} (x : A) : mylist A -> Prop :=
| In_head : forall xs,      InL x (x ::L xs)
| In_tail : forall y xs, InL x xs -> InL x (y ::L xs).

Inductive NoDupL {A : Type} : mylist A -> Prop :=
| ND_nil  : NoDupL nilL
| ND_cons : forall x xs, (~ InL x xs) -> NoDupL xs -> NoDupL (x ::L xs).

Fixpoint lengthL {A : Type} (xs : mylist A) : mynat :=
  match xs with
  | nilL      => O
  | _ ::L tl  => S (lengthL tl)
  end.

Class ring (R : Type) := {
  zero      : R;
  opp       : R -> R;
  one       : R;
  add       : R -> R -> R;
  mul       : R -> R -> R;

  one_neq_zero  : one <> zero;

  add_comm  : forall x y,    add x y = add y x;
  add_assoc : forall x y z,  add (add x y) z = add x (add y z);
  add_zero  : forall x,      add x zero = x;
  add_opp   : forall x,      add x (opp x) = zero;

  mul_comm  : forall x y,    mul x y = mul y x;
  mul_assoc : forall x y z,  mul (mul x y) z = mul x (mul y z);
  mul_one   : forall x,      mul x one = x;
  dist_l    : forall x y z,  mul x (add y z) = add (mul x y) (mul x z);
  mul_zero  : forall x,      mul x zero = zero;
  
  no_zero_div :
    forall x y, mul x y = zero -> x = zero \/ y = zero
}.

Notation "x +R y" := (add x y) (at level 50, left associativity).
Notation "-R x"    := (opp x)    (at level 35).
Notation "x -R y"  := (add x (opp y)) (at level 55).
Notation "x *R y"  := (mul x y)  (at level 40).

Section Polynomial.
  Context {R : Type} `{ring R}.

  Context {polynomial : Type} `{ring polynomial}.

  Variable degree    : polynomial -> mynat.
  Variable monomial  : mynat -> R -> polynomial.

  Variable eval : polynomial -> R -> R.

  Definition X          : polynomial := monomial (S O) one.
  Definition C (c:R)    : polynomial := monomial O c.
  Definition X_minus (a:R) : polynomial := X +R C (-R a).

  Axiom C_zero : C zero = zero.
  Axiom C_one         : C one = one.

  Axiom deg_zero      : degree zero = O.

  Axiom eval_add     : forall p q x,     eval (p +R q) x = eval p x +R eval q x.
  Axiom eval_mul     : forall p q x,     eval (p *R q) x = eval p x *R eval q x.
  Axiom eval_C       : forall c x,       eval (C c) x   = c.
  Axiom eval_X       : forall x,         eval X x       = x.

  Axiom deg_C        : forall c, c <> zero -> degree (C c) = O.
  Axiom deg_constant : forall p, degree p = O <-> exists c, p = C c.
  Axiom deg_X_minus  : forall a,         degree (X_minus a) = S O.
  Axiom deg_mul      : forall p q,
    p <> zero -> q <> zero ->
    degree (p *R q) = mynat_add (degree p) (degree q).

   Axiom euclid_X_minus :
    forall p a, exists q r,
      p = q *R X_minus a +R r
      /\ degree r = O.

  
  Lemma sub_eq_zero_l `{ring R} : forall a b, a -R b = zero -> a = b.
Proof.
Admitted.

  Lemma root_factor :
    forall p a, eval p a = zero ->
      exists q, p = q *R X_minus a.
Proof.
Admitted.

  Lemma root_transfer :
    forall p q a b,
      p = q *R X_minus a ->
      b <> a ->
      eval p b = zero ->
      eval q b = zero.
Proof.
Admitted.

  Definition root (a:R) (p:polynomial) : Prop := eval p a = zero.

  Theorem roots_le_degree :
    forall p (xs:mylist R),
      NoDupL xs ->
      (forall a, InL a xs -> root a p) ->
      p <> zero ->
      mynat_le (lengthL xs) (degree p).
Proof.
Admitted.

  Fixpoint poly_of_roots (xs : mylist R) : polynomial :=
  match xs with
  | nilL        => one
  | consL a xs' => X_minus a *R poly_of_roots xs'
  end.

  Lemma X_minus_nonzero : forall a, X_minus a <> zero.
Proof.
Admitted.

  Lemma constant_root_zero :
    forall p a, degree p = O -> root a p -> p = zero.
Proof.
Admitted.

  Lemma root_of_product :
    forall p q a, root a (p *R q) -> root a p \/ root a q.
Proof.
Admitted.

  Lemma root_scale_constant :
    forall p c a, c <> zero -> (root a p <-> root a (C c *R p)).
Proof.
Admitted.

  Lemma poly_of_roots_nonzero : forall xs, poly_of_roots xs <> zero.
Proof.
Admitted.

  Lemma deg_poly_of_roots :
    forall xs, degree (poly_of_roots xs) = lengthL xs.
Proof.
Admitted.


  Lemma root_factor_list :
  forall p xs,
    NoDupL xs ->
    (forall a, InL a xs -> root a p) ->
    exists q, p = q *R poly_of_roots xs.
Proof.
Admitted.

  Lemma degree_factorisation :
    forall p xs q,
      p = q *R poly_of_roots xs ->
      q <> zero ->
      degree p = mynat_add (degree q) (lengthL xs).
Proof.
Admitted.

End Polynomial.
