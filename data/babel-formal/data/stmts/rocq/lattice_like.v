Class LatticeLike (A : Type) := {
  le   : A -> A -> Prop;
  inf  : A -> A -> A;
  sup  : A -> A -> A;

  le_refl  : forall x, le x x;
  le_trans : forall x y z, le x y -> le y z -> le x z;
  le_antisym : forall x y, le x y -> le y x -> x = y;

  le_inf_left  : forall a b, le (inf a b) a;
  le_inf_right : forall a b, le (inf a b) b;
  le_inf_intro : forall c a b, le c a -> le c b -> le c (inf a b);

  le_sup_left  : forall a b, le a (sup a b);
  le_sup_right : forall a b, le b (sup a b);
  sup_le_intro : forall a b c, le a c -> le b c -> le (sup a b) c
}.

Section LatticeFacts.
  Context {A : Type} {L : LatticeLike A}.

  Infix "≤" := le (at level 70, no associativity).

  Notation "x ⊓ y" := (inf x y) (at level 40).
  Notation "x ⊔ y" := (sup x y) (at level 50).

  Lemma inf_comm (a b : A) : a ⊓ b = b ⊓ a.
Proof.
Admitted.

  Lemma sup_comm (a b : A) : a ⊔ b = b ⊔ a.
Proof.
Admitted.

  Lemma inf_assoc (a b c : A) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c).
Proof.
Admitted.

  Lemma sup_assoc (a b c : A) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c).
Proof.
Admitted.

  Lemma inf_absorption (a b : A) : a ⊓ (a ⊔ b) = a.
Proof.
Admitted.

  Lemma sup_absorption (a b : A) : a ⊔ (a ⊓ b) = a.
Proof.
Admitted.

End LatticeFacts.
