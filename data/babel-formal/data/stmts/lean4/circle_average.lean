class AddMonoid (R : Type) where
  zero      : R
  add       : R → R → R
  add_zero  : ∀ x, add x zero = x
  add_comm  : ∀ x y, add x y = add y x
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)

namespace CircleAverage
variable {R : Type} [AddMonoid R]

axiom integral       : (R → R) → R
axiom integral_ext   : ∀ (g h : R → R), (∀ θ, g θ = h θ) → integral g = integral h
axiom integral_const : ∀ (c : R), integral (fun _ => c) = c
axiom integral_add   : ∀ (f g : R → R),
  integral (fun θ => AddMonoid.add (f θ) (g θ)) =
  AddMonoid.add (integral f) (integral g)
axiom integral_shift : ∀ (f : R → R) (c : R),
  integral (fun θ => f (AddMonoid.add θ c)) = integral f

def circleMap (c θ : R) : R := AddMonoid.add θ c
noncomputable def circleAverage (f : R → R) (c : R) : R :=
  integral (fun θ => f (circleMap c θ))

theorem circleMap_zero (θ : R) :
  circleMap AddMonoid.zero θ = θ := by sorry
theorem circleAverage_zero (f : R → R) :
  circleAverage f AddMonoid.zero = integral f := by sorry
theorem circleAverage_add (f g : R → R) (c : R) :
  circleAverage (fun z => AddMonoid.add (f z) (g z)) c =
  AddMonoid.add (circleAverage f c) (circleAverage g c) := by sorry
theorem circleAverage_fun_add (f : R → R) (c : R) :
  circleAverage (fun z => f (AddMonoid.add z c)) AddMonoid.zero =
  circleAverage f c := by sorry
theorem circleMap_add (c d θ : R) :
  circleMap (AddMonoid.add c d) θ =
  circleMap c (circleMap d θ) := by sorry
theorem circleAverage_shift (f : R → R) (c d : R) :
  circleAverage f (AddMonoid.add c d) =
  circleAverage (fun z => f (AddMonoid.add z d)) c := by sorry
theorem circleAverage_const (k c : R) :
  circleAverage (fun _ => k) c = k := by sorry
theorem circleAverage_add_const (f : R → R) (k c : R) :
  circleAverage (fun z => AddMonoid.add (f z) k) c =
  AddMonoid.add (circleAverage f c) k := by sorry
theorem circleAverage_comm_add (f g : R → R) (c : R) :
  circleAverage (fun z => AddMonoid.add (f z) (g z)) c =
  circleAverage (fun z => AddMonoid.add (g z) (f z)) c := by sorry
theorem circleAverage_add_assoc (f g h : R → R) (c : R) :
  circleAverage (fun z => AddMonoid.add (AddMonoid.add (f z) (g z)) (h z)) c =
  AddMonoid.add (circleAverage f c)
              (AddMonoid.add (circleAverage g c) (circleAverage h c)) := by sorry
theorem circleAverage_center_comm (f : R → R) (c d : R) :
  circleAverage f (AddMonoid.add c d) =
  circleAverage f (AddMonoid.add d c) := by sorry
theorem circleAverage_center_independent (f : R → R) (c : R) :
  circleAverage f c = integral f := by sorry
theorem circleAverage_center_eq (f : R → R) (c d : R) :
  circleAverage f c = circleAverage f d := by sorry
theorem circleAverage_idempotent (f : R → R) (c : R) :
  circleAverage (fun z => circleAverage f z) c = circleAverage f c := by sorry
theorem circleAverage_of_zero_integral (f : R → R) (c : R) (H : integral f = AddMonoid.zero) :
  circleAverage f c = AddMonoid.zero := by sorry
theorem circleAverage_linear (f g : R → R) (c : R) :
  circleAverage (fun z => AddMonoid.add (f z) (g z)) c =
  AddMonoid.add (circleAverage f c) (circleAverage g c) := by sorry
theorem circleAverage_shift_commute (f : R → R) (c d : R) :
  circleAverage (fun z => f (circleMap d z)) c =
  circleAverage f (AddMonoid.add c d) := by sorry
end CircleAverage
