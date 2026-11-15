Class Field (F : Type) := {
  zero_F    : F;
  one_F     : F;
  add_F     : F -> F -> F;
  mul_F     : F -> F -> F;
  opp_F     : F -> F;
  inv_F     : F -> F;

  add_comm    : forall x y, add_F x y = add_F y x;
  add_assoc   : forall x y z, add_F (add_F x y) z = add_F x (add_F y z);
  add_zero    : forall x, add_F x zero_F = x;
  add_inv_l   : forall x, add_F (opp_F x) x = zero_F;

  mul_comm    : forall x y, mul_F x y = mul_F y x;
  mul_assoc   : forall x y z, mul_F (mul_F x y) z = mul_F x (mul_F y z);
  mul_one_l   : forall x, mul_F one_F x = x;
  mul_inv_l   : forall x, x <> zero_F -> mul_F (inv_F x) x = one_F;

  distrib_l   : forall x y z, mul_F x (add_F y z) = add_F (mul_F x y) (mul_F x z);

  zero_neq_one : zero_F <> one_F;
  inv_nonzero  : forall x, x <> zero_F -> inv_F x <> zero_F;
}.

Section FieldProperties.
  Context {F : Type} {HF : Field F}.

  Infix "+" := add_F.
  Infix "*" := mul_F.
  Notation "- x" := (opp_F x).
  Notation "/ x" := (inv_F x).
  Notation "0" := zero_F.
  Notation "1" := one_F.

  Lemma add_cancel_l (x y z : F) : x + y = x + z -> y = z.
Proof.
Admitted.

  Lemma add_cancel_r (x y z : F) : y + x = z + x -> y = z.
Proof.
Admitted.

  Lemma mul_cancel_l (x y z : F) : x <> 0 -> x * y = x * z -> y = z.
Proof.
Admitted.

  Lemma mul_cancel_r (x y z : F) : x <> 0 -> y * x = z * x -> y = z.
Proof.
Admitted.

  Lemma inv_unique (x y : F) : x <> 0 -> x * y = 1 -> y = inv_F x.
Proof.
Admitted.

  Lemma inv_involutive (x : F) : x <> 0 -> inv_F (inv_F x) = x.
Proof.
Admitted.

End FieldProperties.

Class IsSolvable (G : Type) : Prop.

Section Tower.
  Variable polynomial      : Type -> Type.
  Variable SplittingField  : forall {F : Type}, polynomial F -> Type.
  Variable algebraMap      : forall {F K : Type}, F -> K.
  Variable Splits          : forall {F K : Type}, polynomial F -> (F -> K) -> Prop.
  Variable map_poly        : forall {F K : Type}, polynomial F -> (F -> K) -> polynomial K.
  Variable Gal             : forall {F : Type}, polynomial F -> Type.

  Context {F : Type}.
  Variables p q r s t : polynomial F.
  Variables K L       : Type.

  Variables u v : polynomial F.
  Axiom map_poly_comp :
    forall {F K L : Type} (p : polynomial F)
           (f : F -> K) (g : K -> L),
      map_poly (map_poly p f) g
      = map_poly p (fun x => g (f x)).
  Axiom isSolvable_of_isScalarTower :
    forall {F K : Type} {p q : polynomial F},
      IsSolvable (Gal p) ->
      IsSolvable (Gal (map_poly q (@algebraMap F K))) ->
      IsSolvable (Gal q).

  Axiom isSolvable_map_poly :
    forall {F K : Type} (p : polynomial F),
      IsSolvable (Gal p) ->
      IsSolvable (Gal (map_poly p (@algebraMap F K))).


  Axiom isSolvable_of_splits :
    forall {F K : Type} (p : polynomial F) (f : F -> K),
      Splits p f -> IsSolvable (Gal p).

  Theorem gal_isSolvable_tower
          (hp : IsSolvable (Gal p))
          (hq : IsSolvable (Gal (map_poly q (@algebraMap F (SplittingField p)))))
        : IsSolvable (Gal q).
Proof.
Admitted.

  Theorem gal_isSolvable_double_tower
          (hp : IsSolvable (Gal p))
          (hq : IsSolvable (Gal (map_poly q (@algebraMap F (SplittingField p)))))
          (hr : IsSolvable (Gal (map_poly r (@algebraMap F (SplittingField q)))))
        : IsSolvable (Gal r).
Proof.
Admitted.

  Theorem gal_isSolvable_triple_tower
          (hp : IsSolvable (Gal p))
          (hq : IsSolvable (Gal (map_poly q (@algebraMap F (SplittingField p)))))
          (hr : IsSolvable (Gal (map_poly r (@algebraMap F (SplittingField q)))))
          (hs : IsSolvable (Gal (map_poly s (@algebraMap F (SplittingField r)))))
        : IsSolvable (Gal s).
Proof.
Admitted.

  Theorem gal_isSolvable_quadruple_tower
          (hp : IsSolvable (Gal p))
          (hq : IsSolvable (Gal (map_poly q (@algebraMap F (SplittingField p)))))
          (hr : IsSolvable (Gal (map_poly r (@algebraMap F (SplittingField q)))))
          (hs : IsSolvable (Gal (map_poly s (@algebraMap F (SplittingField r)))))
          (ht : IsSolvable (Gal (map_poly t (@algebraMap F (SplittingField s)))))
        : IsSolvable (Gal t).
Proof.
Admitted.

  Theorem gal_isSolvable_map_poly
          (hp : IsSolvable (Gal p))
        : IsSolvable (Gal (map_poly p (@algebraMap F K))).
Proof.
Admitted.

  Theorem gal_isSolvable_of_split
          (hsplit : Splits p (@algebraMap F (SplittingField p)))
        : IsSolvable (Gal p).
Proof.
Admitted.

  Theorem gal_isSolvable_split_tower
          (hsplit : Splits q (@algebraMap F (SplittingField p)))
        : IsSolvable (Gal q).
Proof.
Admitted.

 Theorem gal_isSolvable_two_step_map
          (hp : IsSolvable (Gal p))
        : IsSolvable
            (Gal (map_poly (map_poly p (@algebraMap F K)) (@algebraMap K L))).
Proof.
Admitted.

  Theorem gal_isSolvable_three_step_map
          {M : Type}
          (hp : IsSolvable (Gal p))
        : IsSolvable
            (Gal
               (map_poly
                  (map_poly
                     (map_poly p (@algebraMap F K))
                             (@algebraMap K L))
                             (@algebraMap L M))).
Proof.
Admitted.

  Theorem gal_isSolvable_map_poly_comp
          (hp : IsSolvable (Gal p))
        : IsSolvable
            (Gal
              (map_poly
                 (map_poly p (@algebraMap F K))
                 (@algebraMap K L))).
Proof.
Admitted.

  Theorem gal_isSolvable_mutual_split
          (hsplit_p : Splits p (@algebraMap F (SplittingField q)))
          (hsplit_q : Splits q (@algebraMap F (SplittingField p)))
        : IsSolvable (Gal p) /\ IsSolvable (Gal q).
Proof.
Admitted.

  Theorem gal_isSolvable_tower_split
          (hsplit_q  : Splits q (@algebraMap F (SplittingField p)))
          (hr        : IsSolvable (Gal (map_poly r (@algebraMap F (SplittingField q)))))
        : IsSolvable (Gal r).
Proof.
Admitted.

  Theorem gal_isSolvable_map_after_split
          (hsplit : Splits p (@algebraMap F (SplittingField p)))
        : IsSolvable (Gal (map_poly p (@algebraMap F K))).
Proof.
Admitted.

End Tower.
