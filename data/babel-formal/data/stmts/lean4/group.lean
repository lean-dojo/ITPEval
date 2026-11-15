class Group (G : Type) where
  inv : G → G
  one : G
  mul : G → G → G
  mul_assoc : ∀ a b c : G, mul a (mul b c) = mul (mul a b) c
  mul_one   : ∀ a : G, mul a one = a
  one_mul   : ∀ a : G, mul one a = a
  mul_inv_l : ∀ a : G, mul (inv a) a = one
  mul_inv_r : ∀ a : G, mul a (inv a) = one

namespace Group

infixl:70 " * " => Group.mul
postfix:max "⁻¹" => Group.inv

class GroupComm (G : Type) [Group G] where
  mul_comm : ∀ a b : G, a * b = b * a

section MulRotate
  variable {G : Type} [Group G] [GroupComm G]

  theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by sorry
end MulRotate
section GroupLemmas
  variable {G : Type} [Group G]

  theorem mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by sorry
  theorem mul_right_cancel (a b c : G) (h : b * a = c * a) : b = c := by sorry
  theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by sorry
  theorem inv_mul (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by sorry
  theorem inv_eq_of_mul_eq_one (a b : G) (h : a * b = one) : b = a⁻¹ := by sorry
end GroupLemmas

class Act (G : Type) (X : Type) [Group G] where
  act : G → X → X
  act_one : ∀ x : X, act one x = x
  act_mul : ∀ g h : G, ∀ x : X, act (g * h) x = act g (act h x)


section ActionLemmas
  variable {G : Type} {X : Type}
  [Group G] [Act G X]

  infixr:73 " • " => Act.act

  theorem act_inv (g : G) (x : X) : g⁻¹ • (g • x) = x := by sorry
  theorem act_inv_r (g : G) (x : X) : g • (g⁻¹ • x) = x := by sorry
  def orbit {G : Type} {X : Type} [Group G] [Act G X] (x : X) : X → Prop :=
    fun y => ∃ g : G, g • x = y

  def stabilizer (x : X) : G → Prop := fun g => g • x = x

  theorem orbit_refl
    (x : X) : orbit (G:=G) x x := by sorry
  theorem orbit_sym (x y : X) (h : orbit (G:=G) x y) : orbit (G:=G) y x := by sorry
  theorem orbit_trans (x y z : X) (h1 : orbit (G:=G) x y) (h2 : orbit (G:=G) y z) : orbit (G:=G) x z := by sorry
  theorem orbit_partition (x y : X) (hxy : orbit (G:=G) x y) (z : X) :
      orbit (G:=G) x z ↔ orbit (G:=G) y z := by sorry
  theorem stabilizer_mul (x : X) (g h : G)
    (hg : stabilizer x g) (hh : stabilizer x h) : stabilizer x (g * h) := by sorry
  theorem stabilizer_inv (x : X) (g : G) (hg : stabilizer x g) : stabilizer x g⁻¹ := by sorry
  theorem stabilizer_one (x : X) : stabilizer (G:=G) x one := by sorry
  theorem stabilizer_conjugate (x : X) (g h : G)
    (hh : stabilizer x h) : stabilizer (g • x) (g * h * g⁻¹) := by sorry
  theorem stabilizer_conjugate_orbit (x y : X) (g : G) (hxy : g • x = y) (h : G) :
      stabilizer y h ↔ stabilizer x (g⁻¹ * h * g) := by sorry
end ActionLemmas

end Group
