Class RField (R : Type) := {
  zero   : R;
  one    : R;
  add    : R -> R -> R;
  opp    : R -> R;
  mul    : R -> R -> R;
  le     : R -> R -> Prop;
  lt     : R -> R -> Prop;
  abs    : R -> R;

  add_comm      : forall x y, add x y = add y x;
  add_assoc     : forall x y z, add (add x y) z = add x (add y z);
  add_zero      : forall x, add x zero = x;
  add_opp       : forall x, add (opp x) x = zero;
  add_right_cancel : forall x y z, add x z = add y z -> x = y;

  mul_comm      : forall x y, mul x y = mul y x;
  mul_assoc     : forall x y z, mul (mul x y) z = mul x (mul y z);
  mul_one       : forall x, mul x one = x;
  dist_l        : forall x y z, mul x (add y z) = add (mul x y) (mul x z);
  opp_involutive : forall x, opp (opp x) = x;

  add_le_compat : forall x y z, le x y -> le (add x z) (add y z);
  mul_le_compat : forall x y z, le zero z -> le x y -> le (mul x z) (mul y z);
  zero_le_one   : le zero one;
  le_total      : forall x y, le x y \/ le y x;
  
  le_dec : forall x y, { le x y } + { ~ le x y };

  le_opp        : forall x y, le x y -> le (opp y) (opp x);
  le_antisymm   : forall x y, le x y -> le y x -> x = y;
  lt_opp        : forall x y, lt x y -> lt (opp y) (opp x);
  le_refl       : forall x, le x x;
  le_trans      : forall x y z, le x y -> le y z -> le x z;
  lt_def        : forall x y, lt x y <-> (le x y /\ x <> y);

  abs_pos       : forall x, le zero  x -> abs x = x;
  abs_neg       : forall x, le x zero -> abs x = opp x;
  abs_nonneg    : forall x, le zero (abs x);
  abs_opp       : forall x, abs (opp x) = abs x;
  abs_triangle  : forall x y, le (abs (add x y)) (add (abs x) (abs y));
}.


Class Integral (R : Type) `{RField R} := {
  sigma       : (R -> Prop) -> (R -> R) -> R;
  sigma_mul_const : forall (D : R -> Prop) (f : R -> R) (c : R),
    sigma D (fun x => mul c (f x)) = mul c (sigma D f);
  sigma_congr : forall D f g,
    (forall x, D x -> f x = g x) -> sigma D f = sigma D g;
  sigma_zero  : forall D, sigma D (fun _ => zero) = zero;
  sigma_add   : forall D f g,
    sigma D (fun x => add (f x) (g x)) = add (sigma D f) (sigma D g);

  sigma_union_disjoint : forall (D E : R -> Prop) (f : R -> R),
    (forall x, D x -> E x -> False) ->
    sigma (fun x => D x \/ E x) f = add (sigma D f) (sigma E f);
  sigma_le : forall D f g,
    (forall x, D x -> le (f x) (g x)) -> le (sigma D f) (sigma D g);
  sigma_dom_congr : forall D E f,
    (forall x, D x <-> E x) -> sigma D f = sigma E f
}.

Section Integrals.
  Variable (R : Type).
  Context `{RField R} `{Integral R}.

  Notation "- x" := (opp x) : integral_scope.
  Infix "+" := add : integral_scope.
  Infix "*" := mul : integral_scope.
  Infix "<=" := le : integral_scope.
  Infix "<"  := lt : integral_scope.
  Open Scope integral_scope.

  Definition Iic (c : R) : R -> Prop := fun x => x <= c.
  Definition Ioi (c : R) : R -> Prop := fun x => c < x.
  Definition Iio (c : R) : R -> Prop := fun x => x < c.
  Definition union (D E : R -> Prop) : R -> Prop := fun x => D x \/ E x.
  Definition inter (D E : R -> Prop) : R -> Prop := fun x => D x /\ E x.

  Lemma lt_irrefl : forall x, ~ lt x x.
Proof.
Admitted.

  Lemma lt_trans_strict : forall x y z, lt x y -> lt y z -> lt x z.
Proof.
Admitted.


  Definition preimage (g : R -> R) (D : R -> Prop) : R -> Prop :=
    fun x => D (g x).

  Lemma preimage_union (D E : R -> Prop) (g : R -> R) (x : R) :
    preimage g (union D E) x <-> preimage g D x \/ preimage g E x.
Proof.
Admitted.

  Lemma preimage_inter (D E : R -> Prop) (g : R -> R) (x : R) :
    preimage g (inter D E) x <-> preimage g D x /\ preimage g E x.
Proof.
Admitted.

  Lemma preimage_neg_Ioi (c x : R) :
    preimage opp (Ioi c) x <-> lt x (opp c).
Proof.
Admitted.

  Lemma preimage_neg_Iic (c x: R) :
     preimage opp (Iic c) x <-> Iic x (opp c).
Proof.
Admitted.

  Lemma preimage_comp (D : R -> Prop) (g h: R -> R) :
    forall x, preimage g (preimage h D) x <-> preimage (fun x => h (g x)) D x.
Proof.
Admitted.

  Lemma integral_neg (D : R -> Prop) (f: R -> R) :
  sigma D (fun x => opp (f x)) = opp (sigma D f).
Proof.
Admitted.

  Lemma integral_sub (D : R -> Prop) (f g: R -> R):
    sigma D (fun x => add (f x) (opp (g x))) = add (sigma D f) (opp (sigma D g)).
Proof.
Admitted.

  Lemma sigma_empty (f : R -> R) :
    sigma (fun _ => False) f = zero.
Proof.
Admitted.

  Lemma sigma_bilinear (D : R -> Prop) (f g: R -> R) (c d: R) :
    sigma D (fun x => add (mul c (f x)) (mul d (g x))) =
      add (mul c (sigma D f)) (mul d (sigma D g)).
Proof.
Admitted.

  Lemma sigma_le_monotone (D : R -> Prop) (f g: R -> R) :
    (forall x, D x -> le (f x) (g x)) ->
    le (sigma D f) (sigma D g).
Proof.
Admitted.

  Lemma sigma_nonneg (D : R -> Prop) (f: R -> R) :
    (forall x, D x -> le zero (f x)) ->
    le zero (sigma D f).
Proof.
Admitted.

  Lemma sigma_split (D : R -> Prop) (P : R -> Prop) (f : R -> R)
  (P_dec : forall x, D x -> P x \/ ~ P x) :
    sigma D f =
      add (sigma (fun x => D x /\ P x) f)
          (sigma (fun x => D x /\ ~ P x) f).
Proof.
Admitted.

  Lemma sigma_preimage_neg_Ioi (f: R -> R) (c: R) :
    sigma (preimage opp (Ioi c)) f = sigma (Iio (opp c)) f.
Proof.
Admitted.

  Lemma sigma_abs_bound {D f} :
    le (abs (sigma D f)) (sigma D (fun x => abs (f x))).
Proof.
Admitted.


End Integrals.
