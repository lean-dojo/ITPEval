-- Statement-only formalization of the Babel-formal topic group. This file contains no proof.

module group where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

infix 2 _↔_

record _↔_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    forward  : A → B
    backward : B → A

record Group {ℓ : Level} (G : Set ℓ) : Set ℓ where
  field
    inv       : G → G
    one       : G
    mul       : G → G → G
    mul-assoc : (a b c : G) →
                mul a (mul b c) ≡ mul (mul a b) c
    mul-one   : (a : G) → mul a one ≡ a
    one-mul   : (a : G) → mul one a ≡ a
    mul-inv-l : (a : G) → mul (inv a) a ≡ one
    mul-inv-r : (a : G) → mul a (inv a) ≡ one

record GroupComm {ℓ : Level} {G : Set ℓ}
                 (S : Group G) : Set ℓ where
  open Group S

  field
    mul-comm : (a b : G) → mul a b ≡ mul b a

module CommutativeGroupStatements
  {ℓ : Level} {G : Set ℓ}
  (S : Group G) (C : GroupComm S) where

  open Group S

  mul-rotate' : Set ℓ
  mul-rotate' =
    (a b c : G) → mul a (mul b c) ≡ mul b (mul c a)

module GroupStatements
  {ℓ : Level} {G : Set ℓ}
  (S : Group G) where

  open Group S

  mul-left-cancel : Set ℓ
  mul-left-cancel =
    (a b c : G) → mul a b ≡ mul a c → b ≡ c

  mul-right-cancel : Set ℓ
  mul-right-cancel =
    (a b c : G) → mul b a ≡ mul c a → b ≡ c

  inv-inv : Set ℓ
  inv-inv =
    (a : G) → inv (inv a) ≡ a

  inv-mul : Set ℓ
  inv-mul =
    (a b : G) → inv (mul a b) ≡ mul (inv b) (inv a)

  inv-eq-of-mul-eq-one : Set ℓ
  inv-eq-of-mul-eq-one =
    (a b : G) → mul a b ≡ one → b ≡ inv a

record Act {ℓG ℓX : Level} {G : Set ℓG}
           (S : Group G) (X : Set ℓX) : Set (ℓG ⊔ ℓX) where
  open Group S

  field
    act     : G → X → X
    act-one : (x : X) → act one x ≡ x
    act-mul : (g h : G) (x : X) →
              act (mul g h) x ≡ act g (act h x)

module ActionStatements
  {ℓG ℓX : Level} {G : Set ℓG} {X : Set ℓX}
  (S : Group G) (A : Act S X) where

  open Group S
  open Act A

  orbit : X → X → Set (ℓG ⊔ ℓX)
  orbit x y = Σ G (λ g → act g x ≡ y)

  stabilizer : X → G → Set ℓX
  stabilizer x g = act g x ≡ x

  act-inv : Set (ℓG ⊔ ℓX)
  act-inv =
    (g : G) (x : X) → act (inv g) (act g x) ≡ x

  act-inv-r : Set (ℓG ⊔ ℓX)
  act-inv-r =
    (g : G) (x : X) → act g (act (inv g) x) ≡ x

  orbit-refl : Set (ℓG ⊔ ℓX)
  orbit-refl =
    (x : X) → orbit x x

  orbit-sym : Set (ℓG ⊔ ℓX)
  orbit-sym =
    (x y : X) → orbit x y → orbit y x

  orbit-trans : Set (ℓG ⊔ ℓX)
  orbit-trans =
    (x y z : X) → orbit x y → orbit y z → orbit x z

  orbit-partition : Set (ℓG ⊔ ℓX)
  orbit-partition =
    (x y : X) → orbit x y → (z : X) →
    orbit x z ↔ orbit y z

  stabilizer-mul : Set (ℓG ⊔ ℓX)
  stabilizer-mul =
    (x : X) (g h : G) →
    stabilizer x g →
    stabilizer x h →
    stabilizer x (mul g h)

  stabilizer-inv : Set (ℓG ⊔ ℓX)
  stabilizer-inv =
    (x : X) (g : G) →
    stabilizer x g →
    stabilizer x (inv g)

  stabilizer-one : Set ℓX
  stabilizer-one =
    (x : X) → stabilizer x one

  stabilizer-conjugate : Set (ℓG ⊔ ℓX)
  stabilizer-conjugate =
    (x : X) (g h : G) →
    stabilizer x h →
    stabilizer (act g x) (mul (mul g h) (inv g))

  stabilizer-conjugate-orbit : Set (ℓG ⊔ ℓX)
  stabilizer-conjugate-orbit =
    (x y : X) (g : G) →
    act g x ≡ y →
    (h : G) →
    stabilizer y h ↔
    stabilizer x (mul (mul (inv g) h) g)
