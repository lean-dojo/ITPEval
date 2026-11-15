class AbsField (R : Type) where
  zero  : R
  one   : R
  add   : R → R → R
  mul   : R → R → R
  opp   : R → R
  abs   : R → R
  le    : R → R → Prop
  lt    : R → R → Prop


  NatAlt     : Type
  NatAltle   : NatAlt → NatAlt → Prop
  NatAltMax  : NatAlt → NatAlt → NatAlt
  le_max_left  : ∀ x y, NatAltle x (NatAltMax x y)
  le_max_right : ∀ x y, NatAltle y (NatAltMax x y)

  add_comm  : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero  : ∀ x, add x zero = x
  add_opp   : ∀ x, add x (opp x) = zero
  opp_add   : ∀ x y, opp (add x y) = add (opp x) (opp y)
  mul_comm  : ∀ x y, mul x y = mul y x
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_one   : ∀ x, mul x one = x

  le_refl   : ∀ x, le x x
  le_trans  : ∀ x y z, le x y → le y z → le x z
  add_le_add : ∀ a b c d, le a b → le c d → le (add a c) (add b d)

  abs_nonneg : ∀ x, le zero (abs x)
  abs_triangle : ∀ x y, le (abs (add x y)) (add (abs x) (abs y))
  abs_opp : ∀ x, abs (opp x) = abs x
  abs_sub_symm : ∀ x y, abs (add x (opp y)) = abs (add y (opp x))


  sub_decomp : ∀ x y z, add x (opp z) = add (add x (opp y)) (add y (opp z))
  sub_eq_zero : ∀ x y, add x (opp y) = zero → x = y

  eq_of_forall_eps2 : ∀ x, (∀ eps, lt zero eps → le (abs x) (add eps eps)) → x = zero

namespace Limits

variable {R : Type} [AR : AbsField R]




def sub (x y : R) : R := AbsField.add x (AbsField.opp y)

def limit (u : (AbsField.NatAlt (R := R)) → R) (l : R) : Prop :=
  ∀ eps : R, AbsField.lt AbsField.zero eps →
    ∃ N : AbsField.NatAlt (R := R),
      ∀ n : AbsField.NatAlt (R := R),
        AbsField.NatAltle (R := R) N n →
          AbsField.le (AbsField.abs (sub (u n) l)) eps

theorem sub_self_zero (x : R) : sub x x = AbsField.zero := by sorry
theorem sub_decomp (x y z : R) : sub x z = AR.add (sub x y) (sub y z) := by sorry
theorem abs_sub_triangle (x y z : R) :
  AbsField.le (AbsField.abs (sub x z)) (AbsField.add (AbsField.abs (sub x y)) (AbsField.abs (sub y z))) := by sorry
theorem abs_sub_nonneg (x y : R) : AR.le AR.zero (AR.abs (sub x y)) := by sorry
theorem limit_unique (u : (AbsField.NatAlt (R := R)) → R) (l m : R) :
  limit u l → limit u m → l = m := by sorry
end Limits
