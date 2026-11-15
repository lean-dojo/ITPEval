class CRing (R : Type) where
  zero  : R
  one   : R
  add   : R → R → R
  mul   : R → R → R
  opp   : R → R

  add_comm  : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero  : ∀ x, add x zero = x
  add_opp   : ∀ x, add x (opp x) = zero

  mul_comm  : ∀ x y, mul x y = mul y x
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_one   : ∀ x, mul x one = x
  dist_l    : ∀ a x y, mul a (add x y) = add (mul a x) (mul a y)
  opp_add   : ∀ x y, opp (add x y) = add (opp x) (opp y)

namespace Ideals

variable {R : Type} [CR : CRing R]
open CRing

infixl:65 "+R" => CRing.add
infixl:70 "*R" => CRing.mul
prefix:100 "-R" => CRing.opp

def IsIdeal (I : R → Prop) : Prop :=
  (I CR.zero) ∧
  (∀ x y, I x → I y → I (x +R y)) ∧
  (∀ x, I x → I (-R x)) ∧
  (∀ a x, I x → I (a *R x))

def Inter {ι : Type} (F : ι → (R → Prop)) : R → Prop :=
  fun x => ∀ i, F i x

theorem inter_isIdeal {ι : Type} (F : ι → (R → Prop))
  (h : ∀ i, IsIdeal (F i)) : IsIdeal (Inter F) := by sorry
def sum (I J : R → Prop) : R → Prop :=
  fun x => ∃ a b, I a ∧ J b ∧ x = a +R b

theorem sum_isIdeal (I J : R → Prop) (hI : IsIdeal I) (hJ : IsIdeal J) :
  IsIdeal (sum I J) := by sorry
end Ideals
