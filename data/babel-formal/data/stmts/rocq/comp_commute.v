Section CompCommute.
  Universes u v w.
  Definition comp {α β γ : Type} (g : β -> γ) (f : α -> β) : α -> γ := fun x => g (f x).
  Definition id {α : Type} : α -> α := fun x => x.

  Class FunProps := {
    comp_assoc : forall {α β γ δ} (h : γ -> δ) (g : β -> γ) (f : α -> β), comp h (comp g f) = comp (comp h g) f;
    comp_id_l  : forall {α β} (f : α -> β), comp (@id β) f = f;
    comp_id_r  : forall {α β} (f : α -> β), comp f (@id α) = f
  }.

  Definition commute {α : Type} (f g : α -> α) : Prop := comp f g = comp g f.

  Context {FP : FunProps}.

  Lemma commute_symm : forall {α} (f g : α -> α), commute f g -> commute g f.
Proof.
Admitted.

  Lemma commute_with_id_l : forall {α} (f : α -> α), commute f (@id α).
Proof.
Admitted.

  Lemma commute_with_id_r : forall {α} (f : α -> α), commute (@id α) f.
Proof.
Admitted.

  Lemma commute_refl : forall {α} (f : α -> α), commute f f.
Proof.
Admitted.

  Lemma commute_congr : forall {α} (f1 f2 g1 g2 : α -> α),
    f1 = f2 -> g1 = g2 -> commute f1 g1 -> commute f2 g2.
Proof.
Admitted.

  Lemma commute_transport_left_id : forall {α} (f g : α -> α),
    commute f g -> commute (comp (@id α) f) g.
Proof.
Admitted.

  Lemma commute_transport_right_id : forall {α} (f g : α -> α),
    commute f g -> commute f (comp (@id α) g).
Proof.
Admitted.

End CompCommute.
