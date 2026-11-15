Inductive mynat : Type :=
| O : mynat
| S : mynat -> mynat.

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

Fixpoint mapL {A B} (f : A -> B) (xs : mylist A) : mylist B :=
  match xs with
  | nilL => nilL
  | consL x xs => consL (f x) (mapL f xs)
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

  no_zero_div : forall x y, mul x y = zero -> x = zero \/ y = zero
}.

Notation "x +R y" := (add x y) (at level 50, left associativity).
Notation "-R x"    := (opp x)    (at level 35).
Notation "x -R y"  := (add x (opp y)) (at level 55).
Notation "x *R y"  := (mul x y)  (at level 40).

Section Probability.
  Context {R : Type} `{ring R}.
  Variable Omega : Type.

  Definition event := Omega -> Prop.
  Definition ev_false : event := fun _ => False.
  Definition ev_true  : event := fun _ => True.
  Definition ev_inter (A B : event) : event := fun w => A w /\ B w.
  Definition ev_union (A B : event) : event := fun w => A w \/ B w.
  Definition ev_compl (A : event)   : event := fun w => ~ A w.
  Definition ev_diff  (A B : event) : event := fun w => A w /\ ~ B w.

  Definition disjoint (A B : event) : Prop := forall w, ~ (A w /\ B w).

  Inductive pairwise_disjoint : mylist event -> Prop :=
  | pd_nil  : pairwise_disjoint nilL
  | pd_one  : forall A, pairwise_disjoint (A ::L nilL)
  | pd_cons : forall A B xs,
      disjoint A B -> (forall C, InL C (B ::L xs) -> disjoint A C) ->
      pairwise_disjoint (B ::L xs) ->
      pairwise_disjoint (A ::L B ::L xs).

  Fixpoint bigUnion (xs : mylist event) : event :=
    match xs with
    | nilL        => ev_false
    | consL A xs' => ev_union A (bigUnion xs')
    end.

  Variable prob : event -> R.

  Axiom prob_ext : forall A B, (forall w, A w <-> B w) -> prob A = prob B.
  Axiom prob_false : prob ev_false = zero.
  Axiom prob_true  : prob ev_true  = one.
  Axiom prob_union : forall A B,
    prob (ev_union A B) = prob A +R (prob B +R -R (prob (ev_inter A B))).
  Axiom prob_compl : forall A, prob (ev_compl A) = one +R -R (prob A).

  Axiom classic : forall P:Prop, P \/ ~ P.

  Variable cprob : event -> event -> R.
  Axiom cprob_mul : forall A B, prob (ev_inter A B) = cprob A B *R prob B.

  Definition indep (A B : event) : Prop :=
    prob (ev_inter A B) = prob A *R prob B.


  Axiom opp_zero  : opp zero = zero.
  Axiom opp_opp   : forall x, opp (opp x) = x.
  Axiom opp_mul_right : forall x y, x *R (opp y) = opp (x *R y).
  Axiom opp_mul_left  : forall x y, (opp x) *R y = opp (x *R y).

  Axiom prob_union_disjoint : forall A B, disjoint A B -> prob (ev_union A B) = prob A +R prob B.
  Axiom disjoint_head_tail : forall A xs, pairwise_disjoint (A ::L xs) -> disjoint A (bigUnion xs).

  Lemma prob_union_comm A B :
    prob (ev_union A B) = prob (ev_union B A).
Proof.
Admitted.

  Lemma prob_union_idem A : prob (ev_union A A) = prob A.
Proof.
Admitted.

  Lemma prob_diff A B : prob (ev_diff A B) = prob A -R prob (ev_inter A B).
Proof.
Admitted.

  Lemma bayes_symm A B : cprob A B *R prob B = cprob B A *R prob A.
Proof.
Admitted.

  Lemma law_total_prob A B :
    prob A = cprob A B *R prob B +R cprob A (ev_compl B) *R prob (ev_compl B).
Proof.
Admitted.

  Lemma prob_union_indep A B : indep A B ->
    prob (ev_union A B) = prob A +R (prob B +R -R (prob A *R prob B)).
Proof.
Admitted.

  Lemma indep_symm A B : indep A B -> indep B A.
Proof.
Admitted.

  Lemma indep_compl_right A B : indep A B -> indep A (ev_compl B).
Proof.
Admitted.

  Lemma indep_compl_left A B : indep A B -> indep (ev_compl A) B.
Proof.
Admitted.

  Axiom indep_compl_both : forall A B, indep A B -> indep (ev_compl A) (ev_compl B).

  Fixpoint fold_add (xs : mylist R) : R :=
    match xs with
    | nilL => zero
    | consL x xs' => x +R fold_add xs'
    end.

  Lemma prob_bigUnion_disjoint : forall xs,
    pairwise_disjoint xs -> prob (bigUnion xs) = fold_add (mapL prob xs).
Proof.
Admitted.

  Lemma prob_bigUnion_disjoint_zero : forall xs,
    pairwise_disjoint xs -> (forall A, InL A xs -> prob A = zero) -> prob (bigUnion xs) = zero.
Proof.
Admitted.

  Axiom inclusion_exclusion_three : forall A B C,
    prob (ev_union (ev_union A B) C)
      = prob A +R (prob B +R (prob C +R -R (prob (ev_inter A B) +R (prob (ev_inter A C) +R (prob (ev_inter B C) +R -R (prob (ev_inter (ev_inter A B) C))))))).

End Probability.
