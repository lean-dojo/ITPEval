class CompleteOrderedField where
  R       : Type
  NatAlt  : Type
  zero_nat : NatAlt
  Succ : NatAlt -> NatAlt
  NatAltle : NatAlt -> NatAlt -> Prop

  zero    : R
  one     : R
  add     : R → R → R
  mul     : R → R → R
  opp     : R → R
  inv     : R → R
  Rle     : R → R → Prop
  Rlt     : R → R → Prop
  Rabs    : R → R
  INR     : NatAlt → R

  NatAltle_n : ∀ n : NatAlt, NatAltle n n
  le_succ_of_le : ∀ n m: NatAlt, NatAltle n m → NatAltle n (Succ m)
  le_succ : ∀ n : NatAlt, NatAltle n (Succ n)

  add_comm      : ∀ x y : R, add x y = add y x
  add_assoc     : ∀ x y z : R, add (add x y) z = add x (add y z)
  add_zero      : ∀ x : R, add x zero = x
  add_opp       : ∀ x : R, add (opp x) x = zero
  mul_comm      : ∀ x y : R, mul x y = mul y x
  mul_assoc     : ∀ x y z : R, mul (mul x y) z = mul x (mul y z)
  mul_one       : ∀ x : R, mul x one = x
  dist_l        : ∀ x y z : R, mul x (add y z) = add (mul x y) (mul x z)
  sub_zero      : ∀ x : R, add x (opp zero) = x
  Rle_refl      : ∀ x : R, Rle x x
  Rle_trans     : ∀ x y z : R, Rle x y → Rle y z → Rle x z
  Rle_antisym   : ∀ x y : R, Rle x y → Rle y x → x = y
  Rlt_def       : ∀ x y : R, Rlt x y ↔ (Rle x y ∧ x ≠ y)
  Rle_abs       : ∀ x : R, Rle (add x (opp zero)) (Rabs x)
  Rinv_0_lt_compat : ∀ x : R, Rlt zero x → Rlt zero (inv x)
  Rplus_le_compat_l : ∀ x y z : R, Rle y z → Rle (add x y) (add x z)
  Rinv_involutive   : ∀ x : R, Rlt zero x → inv (inv x) = x
  INR_pos       : ∀ n, Rlt zero (INR (Succ n))
  INR_le        : ∀ m n, (NatAltle m n) → Rle (INR m) (INR n)
  INR_0         : INR zero_nat = zero
  INR_S         : ∀ n, INR (Succ n) = add (INR n) one
  Rtotal_order  : ∀ x y : R, Rlt x y ∨ x = y ∨ Rlt y x
  Rle_inv_contravar : ∀ a b : R, Rlt zero a → Rlt zero b → Rle a b → Rle (inv b) (inv a)
  eps_between   : ∀ x y : R, Rlt x y → ∃ eps, Rlt zero eps ∧ Rlt (add x eps) y
  archimedean   : ∀ x : R, ∃ n, Rle x (INR n)
  completeness  : ∀ (A : R → Prop),
    (∃ ub, ∀ a, A a → Rle ub a) →
    ∃ sup, (∀ a, A a → Rle a sup) ∧ ∀ y, (∀ a, A a → Rle a y) → Rle sup y

namespace SupInf

variable [F : CompleteOrderedField]
open CompleteOrderedField (R zero one add mul opp inv Rle Rlt Rabs INR NatAltle)

infixl:65 " + " => add
infixl:70 " * " => mul
prefix:100 "-" => opp
notation x " - " y:65 => add x (opp y)
prefix:100 "/" => inv
infixl:70 " <= " => NatAltle
infixl:70 " <=R " => Rle
infixl:70 " <R " => Rlt
infixl:70 " >R " => (fun x y => Rlt y x)
notation "|" x "|" => Rabs x


local notation "R" => F.R

def up_bounds (A : R → Prop) : R → Prop :=
  fun x => ∀ a, A a → a <=R x

def is_maximum (a : R) (A : R → Prop) : Prop :=
  A a ∧ up_bounds A a

infix:70 " is_a_max_of " => is_maximum

theorem add_sub_cancel_r (a b : R) :
    a + (b - a) = b := by sorry
theorem Rabs_pos (t : R) : t <=R |t| := by sorry
theorem unique_max (A : R → Prop) (x y : R) :
    x is_a_max_of A → y is_a_max_of A → x = y := by sorry
def low_bounds (A : R → Prop) : R → Prop :=
  fun x => ∀ a, A a → x <=R a

def is_inf (x : R) (A : R → Prop) : Prop :=
  is_maximum x (low_bounds A)

infix:70 " is_an_inf_of " => is_inf

axiom classic : ∀ P : Prop, P ∨ ¬P

theorem inf_lt (A : R → Prop) (x : R) :
    x is_an_inf_of A → ∀ y, x <R y → ∃ a, A a ∧ a <R y := by sorry
theorem le_of_le_add_eps (x y : R) :
    (∀ eps, eps >R F.zero → y <=R (x + eps)) → y <=R x := by sorry
def limit (u : F.NatAlt → R) (l : R) : Prop :=
  ∀ eps, eps >R F.zero → ∃ N : F.NatAlt, ∀ n : F.NatAlt, N <= n → |u n - l| <=R eps

theorem le_lim (x y : R) (u : F.NatAlt → R) :
    limit u x → (∀ n : F.NatAlt, y <=R u n) → y <=R x := by sorry
theorem inv_succ_pos (n : F.NatAlt) : F.zero <R /F.INR (F.Succ n) := by sorry
theorem limit_inv_succ (eps : R) (Heps : eps >R F.zero) :
    ∃ N, ∀ n : F.NatAlt, N <= n → /F.INR (F.Succ n) <=R eps := by sorry
end SupInf
