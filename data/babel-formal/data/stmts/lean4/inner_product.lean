namespace Linear

class Field (R : Type) where
  zero    : R
  one     : R
  add     : R → R → R
  mul     : R → R → R
  opp     : R → R

  add_comm    : ∀ x y, add x y = add y x
  add_assoc   : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero    : ∀ x, add x zero = x
  zero_add    : ∀ x, add zero x = x
  add_opp     : ∀ x, add x (opp x) = zero

  mul_comm    : ∀ x y, mul x y = mul y x
  mul_assoc   : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_one     : ∀ x, mul x one = x
  dist_l      : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)

  opp_add     : ∀ x y, opp (add x y) = add (opp x) (opp y)
  mul_opp_one : ∀ x, mul (opp one) x = opp x
  opp_opp     : ∀ x, opp (opp x) = x

infixl:65  "+R"  => Field.add
infixl:70  "*R"  => Field.mul
prefix:100 "-R"  => Field.opp

class VSpace (R : Type) [Field R] (V : Type) where
  zeroV : V
  addV  : V → V → V
  oppV  : V → V
  smul  : R → V → V

  addV_comm  : ∀ u v, addV u v = addV v u
  addV_assoc : ∀ u v w, addV (addV u v) w = addV u (addV v w)
  addV_zero  : ∀ u, addV u zeroV = u
  addV_opp   : ∀ u, addV u (oppV u) = zeroV

  smul_addV  : ∀ a u v, smul a (addV u v) = addV (smul a u) (smul a v)
  addR_smul  : ∀ a b u, smul (a +R b) u = addV (smul a u) (smul b u)
  mul_smul   : ∀ a b u, smul (a *R b) u = smul a (smul b u)
  one_smul   : ∀ u, smul Field.one u = u
  smul_zero  : ∀ a, smul a zeroV = zeroV
  opp_smul_one : ∀ u, oppV u = smul (Field.opp Field.one) u

infixl:65  "+V"  => VSpace.addV
prefix:100 "-V"  => VSpace.oppV
notation:70 a " •V " u => VSpace.smul a u

def subV {R : Type} {V : Type} [Field R] [VSpace R V] (u v : V) : V :=
  VSpace.addV (R := R) (V := V) u (VSpace.oppV (R := R) (V := V) v)
infixl:65  " -V " => subV

class Inner (R : Type) (V : Type) [Field R] [VSpace R V] where
  ip : V → V → R

  lin_left_add  : ∀ u v w,
    ip (VSpace.addV (R := R) (V := V) u v) w = (ip u w) +R (ip v w)
  lin_left_smul : ∀ a u v,
    ip (VSpace.smul (R := R) (V := V) a u) v = a *R (ip u v)

  lin_right_add  : ∀ u v w,
    ip u (VSpace.addV (R := R) (V := V) v w) = (ip u v) +R (ip u w)
  lin_right_smul : ∀ a u v,
    ip u (VSpace.smul (R := R) (V := V) a v) = a *R (ip u v)

  symm : ∀ u v, ip u v = ip v u


variable {R : Type} {V : Type}
variable [Field R] [VSpace R V] [Inner R V]

theorem ip_neg_left (u v : V) :
  Inner.ip (R := R) (V := V)
    (VSpace.oppV (R := R) (V := V) u) v
    = Field.opp (Inner.ip (R := R) (V := V) u v) := by sorry
theorem ip_neg_right (u v : V) :
  Inner.ip (R := R) (V := V) u
    (VSpace.oppV (R := R) (V := V) v)
    = Field.opp (Inner.ip (R := R) (V := V) u v) := by sorry
theorem ip_add_add (u v : V) :
  Inner.ip (R := R) (V := V)
      (VSpace.addV (R := R) (V := V) u v)
      (VSpace.addV (R := R) (V := V) u v)
    = ((Inner.ip (R := R) (V := V) u u +R Inner.ip (R := R) (V := V) v u)
       +R (Inner.ip (R := R) (V := V) u v +R Inner.ip (R := R) (V := V) v v)) := by sorry
theorem ip_sub_sub (u v : V) :
  Inner.ip (R := R) (V := V)
      (subV (R := R) (V := V) u v)
      (subV (R := R) (V := V) u v)
    = ((Inner.ip (R := R) (V := V) u u +R Field.opp (Inner.ip (R := R) (V := V) v u))
       +R (Field.opp (Inner.ip (R := R) (V := V) u v) +R Inner.ip (R := R) (V := V) v v)) := by sorry
theorem pythagoras (u v : V)
  (h : Inner.ip (R := R) (V := V) u v = Field.zero) :
  Inner.ip (R := R) (V := V)
      (VSpace.addV (R := R) (V := V) u v)
      (VSpace.addV (R := R) (V := V) u v)
    = (Inner.ip (R := R) (V := V) u u +R Inner.ip (R := R) (V := V) v v) := by sorry
theorem parallelogram (u v : V) :
  (Inner.ip (R := R) (V := V)
      (VSpace.addV (R := R) (V := V) u v)
      (VSpace.addV (R := R) (V := V) u v)
     +R Inner.ip (R := R) (V := V)
          (subV (R := R) (V := V) u v)
          (subV (R := R) (V := V) u v))
    = (((Inner.ip (R := R) (V := V) u u +R Inner.ip (R := R) (V := V) v u)
         +R (Inner.ip (R := R) (V := V) u v +R Inner.ip (R := R) (V := V) v v))
       +R ((Inner.ip (R := R) (V := V) u u +R Field.opp (Inner.ip (R := R) (V := V) v u))
           +R ((Field.opp (Inner.ip (R := R) (V := V) u v))
               +R Inner.ip (R := R) (V := V) v v))) := by sorry
end Linear
