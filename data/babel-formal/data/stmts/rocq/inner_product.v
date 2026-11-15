Class Field := {
  R0    : Type;
  zeroR : R0;
  oneR  : R0;
  addR  : R0 -> R0 -> R0;
  mulR  : R0 -> R0 -> R0;
  oppR  : R0 -> R0;

  addR_comm  : forall x y, addR x y = addR y x;
  addR_assoc : forall x y z, addR (addR x y) z = addR x (addR y z);
  addR_zero  : forall x, addR x zeroR = x;
  zeroR_add  : forall x, addR zeroR x = x;
  addR_opp   : forall x, addR x (oppR x) = zeroR;

  mulR_comm  : forall x y, mulR x y = mulR y x;
  mulR_assoc : forall x y z, mulR (mulR x y) z = mulR x (mulR y z);
  mulR_one   : forall x, mulR x oneR = x;
  distR_l    : forall x y z, mulR x (addR y z) = addR (mulR x y) (mulR x z);

  oppR_add   : forall x y, oppR (addR x y) = addR (oppR x) (oppR y);
  mulR_opp_one : forall x, mulR (oppR oneR) x = oppR x;
  oppR_opp : forall x, oppR (oppR x) = x
}.

Section Linear.
  Context {F : Field}.

  Infix "+R" := addR (at level 65).
  Infix "*R" := mulR (at level 70).
  Notation "-R x" := (oppR x) (at level 100).

  Class VSpace := {
    V0     : Type;
    zeroV  : V0;
    addV   : V0 -> V0 -> V0;
    oppV   : V0 -> V0;
    smul   : R0 -> V0 -> V0;

    addV_comm  : forall u v, addV u v = addV v u;
    addV_assoc : forall u v w, addV (addV u v) w = addV u (addV v w);
    addV_zero  : forall u, addV u zeroV = u;
    addV_opp   : forall u, addV u (oppV u) = zeroV;

    smul_addV  : forall a u v, smul a (addV u v) = addV (smul a u) (smul a v);
    addR_smul  : forall a b u, smul (a +R b) u = addV (smul a u) (smul b u);
    mul_smul   : forall a b u, smul (a *R b) u = smul a (smul b u);
    one_smul   : forall u, smul oneR u = u;
    smul_zeroV : forall a, smul a zeroV = zeroV;
    opp_smul_one : forall u, oppV u = smul (oppR oneR) u
  }.

  Infix "+V" := addV (at level 65).
  Notation "-V x" := (oppV x) (at level 100).
  Notation "a •V x" := (smul a x) (at level 70).
  Definition subV {VS : VSpace} (u v : V0) := addV u (oppV v).
  Infix "-V" := subV (at level 65).

  Class Inner `{VS : VSpace} := {
    ip : V0 -> V0 -> R0;

    lin_left_add  : forall u v w, (ip (u +V v) w) = ((ip u w) +R (ip v w));
    lin_left_smul : forall a u v, (ip (a •V u) v) = (a *R (ip u v));

    lin_right_add  : forall u v w, (ip u (v +V w)) = ((ip u v) +R (ip u w));
    lin_right_smul : forall a u v, (ip u (a •V v)) = (a *R (ip u v));

    symm : forall u v, ip u v = ip v u
  }.

    Context `{VS : VSpace} `{IN : Inner}.

    Notation "⟪ x , y ⟫" := (ip x y) (at level 80).

    Lemma ip_neg_left : forall u v, ⟪-V u, v⟫ = -R ⟪u, v⟫.
Proof.
Admitted.

    Lemma ip_neg_right : forall u v, ⟪u, -V v⟫ = -R ⟪u, v⟫.
Proof.
Admitted.

    Lemma ip_add_add : forall u v,
      ⟪u +V v, u +V v⟫ = ((⟪u,u⟫ +R ⟪v,u⟫) +R (⟪u,v⟫ +R ⟪v,v⟫)).
Proof.
Admitted.

    Lemma ip_sub_sub : forall u v,
      ⟪u -V v, u -V v⟫ = ((⟪u,u⟫ +R (-R ⟪v,u⟫)) +R ((-R ⟪u,v⟫) +R ⟪v,v⟫)).
Proof.
Admitted.

    Lemma pythagoras : forall u v,
      ⟪u,v⟫ = zeroR ->
      ⟪u +V v, u +V v⟫ = (⟪u,u⟫ +R ⟪v,v⟫).
Proof.
Admitted.

    Lemma parallelogram : forall u v,
      (⟪u +V v, u +V v⟫ +R ⟪u -V v, u -V v⟫)
        = (((⟪u,u⟫ +R ⟪v,u⟫) +R (⟪u,v⟫ +R ⟪v,v⟫))
           +R ((⟪u,u⟫ +R (-R ⟪v,u⟫)) +R ((-R ⟪u,v⟫) +R ⟪v,v⟫))).
Proof.
Admitted.

End Linear.
