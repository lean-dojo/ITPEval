Section SetAlgebra.
  Variable X : Type.
  Axiom classic : forall P:Prop, P \/ ~P.

  Definition sUnion (A B : X -> Prop) : X -> Prop := fun x => A x \/ B x.
  Definition sInter (A B : X -> Prop) : X -> Prop := fun x => A x /\ B x.
  Definition sCompl (A : X -> Prop) : X -> Prop := fun x => ~ A x.

  Lemma inter_distrib_left (A B C : X -> Prop) :
    forall x, (sInter A (sUnion B C)) x <-> (sUnion (sInter A B) (sInter A C)) x.
Proof.
Admitted.

  Lemma inter_distrib_right (A B C : X -> Prop) :
    forall x, (sInter (sUnion A B) C) x <-> (sUnion (sInter A C) (sInter B C)) x.
Proof.
Admitted.

  Lemma de_morgan_union (A B : X -> Prop) :
    forall x, (sCompl (sUnion A B)) x <-> (sInter (sCompl A) (sCompl B)) x.
Proof.
Admitted.

  Lemma de_morgan_inter (A B : X -> Prop) :
    forall x, (sCompl (sInter A B)) x <-> (sUnion (sCompl A) (sCompl B)) x.
Proof.
Admitted.

End SetAlgebra.
