inductive mynat : Type
| O  : mynat
| S  : mynat → mynat
deriving DecidableEq

open mynat

def mynat_add : mynat → mynat → mynat
| O,        m => m
| (S n'),   m => S (mynat_add n' m)

theorem mynat_add_O_left (m : mynat) :
  mynat_add O m = m := rfl

theorem mynat_add_S_left (n m : mynat) :
  mynat_add (S n) m = S (mynat_add n m) := rfl

inductive mynat_le : mynat → mynat → Prop
| le_n  : ∀ n, mynat_le n n
| le_S  : ∀ n m, mynat_le n m → mynat_le n (S m)

open mynat_le

theorem mynat_zero_le (n : mynat) : mynat_le O n := by sorry
theorem mynat_add_zero_r : ∀ n, mynat_add n O = n := by sorry
theorem mynat_succ_le_succ {n m : mynat} :
  mynat_le n m → mynat_le (S n) (S m) := by sorry
theorem mynat_add_S_r : ∀ m n, mynat_add m (S n) = S (mynat_add m n) := by sorry
theorem mynat_add_comm : ∀ n m, mynat_add n m = mynat_add m n := by sorry

inductive mylist (A : Type) : Type
| nilL  : mylist A
| consL : A → mylist A → mylist A

namespace mylist

notation h "::L" t => mylist.consL  h t

end mylist

open mylist


inductive InL {A : Type} (x : A) : mylist A → Prop
| In_head : ∀ xs, InL x (x ::L xs)
| In_tail : ∀ y xs, InL (x := x) xs → InL (x := x) (y ::L xs)

inductive NoDupL {A : Type} : mylist A → Prop
| ND_nil  : NoDupL mylist.nilL
| ND_cons : ∀ x xs, (¬ InL x xs) → NoDupL xs → NoDupL (x ::L xs)

def lengthL {A : Type} : mylist A → mynat
| mylist.nilL    => O
| (_ ::L tl)=> S (lengthL tl)

class ring (R : Type) where
  (zero      : R)
  (opp       : R → R)
  (one       : R)
  (add       : R → R → R)
  (mul       : R → R → R)

  (one_neq_zero  : one ≠ zero)

  (add_comm  : ∀ x y,    add x y = add y x)
  (add_assoc : ∀ x y z,  add (add x y) z = add x (add y z))
  (add_zero  : ∀ x,      add x zero = x)
  (add_opp   : ∀ x,      add x (opp x) = zero)

  (mul_comm  : ∀ x y,    mul x y = mul y x)
  (mul_assoc : ∀ x y z,  mul (mul x y) z = mul x (mul y z))
  (mul_one   : ∀ x,      mul x one = x)
  (dist_l    : ∀ x y z,  mul x (add y z) = add (mul x y) (mul x z))
  (mul_zero  : ∀ x,      mul x zero = zero)

  (no_zero_div :
    ∀ x y, mul x y = zero → x = zero ∨ y = zero)

notation:35 "-R " x   => ring.opp x
section Polynomial

variable {R : Type} [rR : ring R]
variable {polynomial : Type} [rP : ring polynomial]


variable (degree    : polynomial → mynat)
variable (monomial  : mynat → R → polynomial)
variable (eval      : polynomial → R → R)



local notation:55 x " -R " y => rR.add x (rR.opp y)


def X (monomial : mynat → R → polynomial) : polynomial :=
  monomial (S O) rR.one

def C (monomial : mynat → R → polynomial) (c : R) : polynomial :=
  monomial O c

def X_minus (monomial : mynat → R → polynomial) (a : R) : polynomial :=
  rP.add (X monomial) (C monomial (rR.opp a))


axiom C_zero    : C monomial rR.zero = rP.zero
axiom C_one     : C monomial rR.one  = rP.one

axiom deg_zero  : degree rP.zero = O

axiom eval_add  : ∀ (p q : polynomial) (x : R), eval (rP.add p q) x = rR.add (eval p x) (eval q x)
axiom eval_mul  : ∀ (p q : polynomial) (x : R), eval (rP.mul p q) x = rR.mul (eval p x) (eval q x)
axiom eval_C    : ∀ (c : R) (x : R),   eval (C monomial c) x = c
axiom eval_X    : ∀ (x : R),     eval (X monomial) x     = x

axiom deg_C        : ∀ (c : R), c ≠ rR.zero → degree (C monomial c) = O
axiom deg_constant : ∀ (p : polynomial), degree p = O ↔ ∃ c : R, p = C monomial c
axiom deg_X_minus  : ∀ (a : R), degree (X_minus monomial a) = S O
axiom deg_mul      : ∀ (p q : polynomial), p ≠ rP.zero → q ≠ rP.zero →
                      degree (rP.mul p q) = mynat_add (degree p) (degree q)



axiom euclid_X_minus :
  ∀ p a, ∃ (q r' : polynomial),
    (p = rP.add (rP.mul q (X_minus monomial a)) r') ∧ (degree r' = O)







theorem sub_eq_zero_l : ∀ a b : R, rR.add a (rR.opp b) = rR.zero → a = b := by sorry
def is_root (eval : polynomial → R → R) (a : R) (p : polynomial) : Prop := eval p a = rR.zero




theorem root_factor
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p : polynomial) (a : R) :
  is_root eval a p → ∃ q : polynomial, p = rP.mul q (X_minus monomial a)
:= by sorry
theorem root_transfer
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p q : polynomial) (a b : R) :
  p = rP.mul q (X_minus monomial a) →
  b ≠ a →
  is_root eval b p →
  is_root eval b q
:= by sorry
theorem roots_le_degree
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p : polynomial) (xs : mylist R) :
  NoDupL xs →
  (∀ a, InL a xs → is_root eval a p) →
  p ≠ rP.zero →
  mynat_le (lengthL xs) (degree p)
:= by sorry
def poly_of_roots (monomial : mynat → R → polynomial) : mylist R → polynomial
| mylist.nilL       => rP.one
| mylist.consL a xs => rP.mul (X_minus monomial a) (poly_of_roots monomial xs)


theorem X_minus_nonzero
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial) :
  ∀ a, (X_minus monomial a) ≠ rP.zero := by sorry
theorem constant_root_zero
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p : polynomial) (a : R) :
  degree p = O → is_root eval a p → p = rP.zero := by sorry
theorem root_of_product
  (eval : polynomial → R → R)
  (p q : polynomial) (a : R) :
  is_root eval a (rP.mul p q) → is_root eval a p ∨ is_root eval a q := by sorry
theorem root_scale_constant
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R)
  (p : polynomial) (c a : R) :
  c ≠ rR.zero → (is_root eval a p ↔ is_root eval a (rP.mul (C monomial c) p)) := by sorry
theorem poly_of_roots_nonzero
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial) :
  ∀ (xs : mylist R), poly_of_roots monomial xs ≠ rP.zero := by sorry
theorem deg_poly_of_roots
  (xs : mylist R) :
  degree (poly_of_roots monomial xs) = lengthL xs := by sorry
theorem root_factor_list
  (degree : polynomial → mynat)
  (monomial : mynat → R → polynomial)
  (eval : polynomial → R → R) :
  ∀ (p : polynomial) (xs : mylist R),
    NoDupL xs →
    (∀ a, InL a xs → is_root eval a p) →
    ∃ q, p = rP.mul q (poly_of_roots monomial xs)
:= by sorry
theorem degree_factorisation :
  ∀ (p : polynomial) (xs : mylist R) (q : polynomial),
    p = rP.mul q (poly_of_roots monomial xs) →
    q ≠ rP.zero →
    degree p = mynat_add (degree q) (lengthL xs)
:= by sorry
end Polynomial
