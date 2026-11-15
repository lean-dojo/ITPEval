class Field (R : Type) where
  zero    : R
  one     : R
  add     : R → R → R
  mul     : R → R → R
  opp     : R → R
  add_comm  : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero  : ∀ x, add x zero = x
  add_opp   : ∀ x, add x (opp x) = zero
  mul_comm  : ∀ x y, mul x y = mul y x
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_one   : ∀ x, mul x one = x
  dist_l    : ∀ a x y, mul a (add x y) = add (mul a x) (mul a y)

namespace Lin

variable {R : Type} [FR : Field R]
open Field

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

attribute [simp] VSpace.addV_zero VSpace.smul_zero

infixl:65  "+V"  => VSpace.addV
notation:70 a " •V " u => VSpace.smul a u

structure LMap (V W : Type) [VSpace R V] [VSpace R W] where
  toFun : V → W
  map_add : ∀ u v, toFun (VSpace.addV (R:=R) u v)
             = VSpace.addV (R:=R) (toFun u) (toFun v)
  map_smul : ∀ a u, toFun (VSpace.smul (R:=R) a u)
             = VSpace.smul (R:=R) a (toFun u)

attribute [simp] LMap.map_add LMap.map_smul

variable {V W U : Type}
variable [VSpace R V] [VSpace R W] [VSpace R U]

def ker (L : LMap (R:=R) V W) : V → Prop := fun x => L.toFun x = VSpace.zeroV (R:=R)
def im  (L : LMap (R:=R) V W) : W → Prop := fun y => ∃ x, L.toFun x = y

def comp (g : LMap (R:=R) W U) (f : LMap (R:=R) V W) : LMap (R:=R) V U :=
{ toFun := fun x => g.toFun (f.toFun x)
, map_add := by sorry
theorem ker_add {L : LMap (R:=R) V W} {x y : V} :
  ker L x → ker L y → ker L (VSpace.addV (R:=R) x y) := by sorry
theorem ker_smul {L : LMap (R:=R) V W} {a : R} {x : V} :
  ker L x → ker L (VSpace.smul (R:=R) a x) := by sorry
theorem im_add {L : LMap (R:=R) V W} {y z : W} :
  im L y → im L z → im L (VSpace.addV (R:=R) y z) := by sorry
theorem im_smul {L : LMap (R:=R) V W} {a : R} {y : W} :
  im L y → im L (VSpace.smul (R:=R) a y) := by sorry
end Lin
