Class AddMonoid (R : Type) := {
  zero      : R;
  add       : R -> R -> R;
  add_zero  : forall x, add x zero = x;
  add_comm  : forall x y, add x y = add y x;
  add_assoc : forall x y z, add (add x y) z = add x (add y z)
}.

Section CircleAverage.
  Context {R : Type} {M : AddMonoid R}.

  Axiom integral       : (R -> R) -> R.
  Axiom integral_ext   : forall g h,
      (forall θ, g θ = h θ) ->
      integral g = integral h.
  Axiom integral_const : forall c,
      integral (fun _ => c) = c.
  Axiom integral_add   : forall f g,
      integral (fun θ => add (f θ) (g θ)) =
      add (integral f) (integral g).

  Axiom integral_shift : forall f c,
    integral (fun θ => f (add θ c)) = integral f.


  Definition circleMap (c θ : R) : R := add θ c.

  Definition circleAverage (f : R -> R) (c : R) : R :=
    integral (fun θ => f (circleMap c θ)).

  Lemma circleMap_zero :
    forall θ, circleMap zero θ = θ.
Proof.
Admitted.

  Lemma circleAverage_zero :
    forall f, circleAverage f zero = integral f.
Proof.
Admitted.

  Lemma circleAverage_add :
    forall f g c,
      circleAverage (fun z => add (f z) (g z)) c =
      add (circleAverage f c) (circleAverage g c).
Proof.
Admitted.

  Theorem circleAverage_fun_add :
    forall f c,
      circleAverage (fun z => f (add z c)) zero =
      circleAverage f c.
Proof.
Admitted.

 Lemma circleMap_add :
    forall c d θ,
      circleMap (add c d) θ =
      circleMap c (circleMap d θ).
Proof.
Admitted.

  Lemma circleAverage_shift :
    forall f c d,
      circleAverage f (add c d) =
      circleAverage (fun z => f (add z d)) c.
Proof.
Admitted.

  Lemma circleAverage_const :
    forall k c, circleAverage (fun _ => k) c = k.
Proof.
Admitted.

  Lemma circleAverage_add_const :
    forall f k c,
      circleAverage (fun z => add (f z) k) c =
      add (circleAverage f c) k.
Proof.
Admitted.

  Lemma circleAverage_comm_add :
    forall f g c,
      circleAverage (fun z => add (f z) (g z)) c =
      circleAverage (fun z => add (g z) (f z)) c.
Proof.
Admitted.

  Lemma circleAverage_add_assoc :
    forall f g h c,
      circleAverage (fun z => add (add (f z) (g z)) (h z)) c =
      add (circleAverage f c)
          (add (circleAverage g c) (circleAverage h c)).
Proof.
Admitted.

  Lemma circleAverage_center_comm :
    forall f c d,
      circleAverage f (add c d) =
      circleAverage f (add d c).
Proof.
Admitted.
  Lemma circleAverage_center_independent :
    forall f c,
      circleAverage f c = integral f.
Proof.
Admitted.

  Lemma circleAverage_center_eq :
    forall f c d,
      circleAverage f c = circleAverage f d.
Proof.
Admitted.

  Lemma circleAverage_idempotent :
  forall f c,
    circleAverage (fun z => circleAverage f z) c = circleAverage f c.
Proof.
Admitted.

  Lemma circleAverage_of_zero_integral :
    forall f c,
      integral f = zero -> circleAverage f c = zero.
Proof.
Admitted.

  Lemma circleAverage_linear :
    forall f g c,
      circleAverage (fun z => add (f z) (g z)) c =
      add (circleAverage f c) (circleAverage g c).
Proof.
Admitted.
  
  Lemma circleAverage_shift_commute :
    forall f c d,
      circleAverage (fun z => f (circleMap d z)) c =
      circleAverage f (add c d).
Proof.
Admitted.
End CircleAverage.
