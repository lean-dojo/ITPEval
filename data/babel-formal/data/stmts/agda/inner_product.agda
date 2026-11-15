-- Statement-only formalization of the Babel-formal topic inner_product. This file contains no
-- proof.

module inner_product where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

record Field {ℓ : Level} (R : Set ℓ) : Set ℓ where
  field
    zero : R
    one  : R
    add  : R → R → R
    mul  : R → R → R
    opp  : R → R

    add-comm  : (x y : R) → add x y ≡ add y x
    add-assoc : (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero  : (x : R) → add x zero ≡ x
    zero-add  : (x : R) → add zero x ≡ x
    add-opp   : (x : R) → add x (opp x) ≡ zero

    mul-comm    : (x y : R) → mul x y ≡ mul y x
    mul-assoc   : (x y z : R) → mul (mul x y) z ≡ mul x (mul y z)
    mul-one     : (x : R) → mul x one ≡ x
    distribute  : (x y z : R) →
                  mul x (add y z) ≡ add (mul x y) (mul x z)

    opp-add     : (x y : R) → opp (add x y) ≡ add (opp x) (opp y)
    mul-opp-one : (x : R) → mul (opp one) x ≡ opp x
    opp-opp     : (x : R) → opp (opp x) ≡ x

record VSpace {ℓR ℓV : Level} {R : Set ℓR}
              (F : Field R) (V : Set ℓV) : Set (ℓR ⊔ ℓV) where
  open Field F

  field
    zeroV : V
    addV  : V → V → V
    oppV  : V → V
    smul  : R → V → V

    addV-comm  : (u v : V) → addV u v ≡ addV v u
    addV-assoc : (u v w : V) → addV (addV u v) w ≡ addV u (addV v w)
    addV-zero  : (u : V) → addV u zeroV ≡ u
    addV-opp   : (u : V) → addV u (oppV u) ≡ zeroV

    smul-addV : (a : R) (u v : V) →
                smul a (addV u v) ≡ addV (smul a u) (smul a v)
    add-smul  : (a b : R) (u : V) →
                smul (add a b) u ≡ addV (smul a u) (smul b u)
    mul-smul  : (a b : R) (u : V) →
                smul (mul a b) u ≡ smul a (smul b u)
    one-smul  : (u : V) → smul one u ≡ u
    smul-zero : (a : R) → smul a zeroV ≡ zeroV
    opp-smul-one : (u : V) → oppV u ≡ smul (opp one) u

record Inner {ℓR ℓV : Level} {R : Set ℓR} {V : Set ℓV}
             (F : Field R) (S : VSpace F V) : Set (ℓR ⊔ ℓV) where
  open Field F
  open VSpace S

  field
    ip : V → V → R

    linear-left-add : (u v w : V) →
      ip (addV u v) w ≡ add (ip u w) (ip v w)
    linear-left-smul : (a : R) (u v : V) →
      ip (smul a u) v ≡ mul a (ip u v)

    linear-right-add : (u v w : V) →
      ip u (addV v w) ≡ add (ip u v) (ip u w)
    linear-right-smul : (a : R) (u v : V) →
      ip u (smul a v) ≡ mul a (ip u v)

    symmetric : (u v : V) → ip u v ≡ ip v u

module InnerProductStatements
  {ℓR ℓV : Level} {R : Set ℓR} {V : Set ℓV}
  (F : Field R) (S : VSpace F V) (I : Inner F S) where

  open Field F
  open VSpace S
  open Inner I

  subV : V → V → V
  subV u v = addV u (oppV v)

  ip-neg-left : Set (ℓR ⊔ ℓV)
  ip-neg-left =
    (u v : V) →
    ip (oppV u) v ≡ opp (ip u v)

  ip-neg-right : Set (ℓR ⊔ ℓV)
  ip-neg-right =
    (u v : V) →
    ip u (oppV v) ≡ opp (ip u v)

  ip-add-add : Set (ℓR ⊔ ℓV)
  ip-add-add =
    (u v : V) →
    ip (addV u v) (addV u v) ≡
    add (add (ip u u) (ip v u))
        (add (ip u v) (ip v v))

  ip-sub-sub : Set (ℓR ⊔ ℓV)
  ip-sub-sub =
    (u v : V) →
    ip (subV u v) (subV u v) ≡
    add (add (ip u u) (opp (ip v u)))
        (add (opp (ip u v)) (ip v v))

  pythagoras : Set (ℓR ⊔ ℓV)
  pythagoras =
    (u v : V) →
    ip u v ≡ zero →
    ip (addV u v) (addV u v) ≡ add (ip u u) (ip v v)

  parallelogram : Set (ℓR ⊔ ℓV)
  parallelogram =
    (u v : V) →
    add (ip (addV u v) (addV u v))
        (ip (subV u v) (subV u v)) ≡
    add (add (add (ip u u) (ip v u))
             (add (ip u v) (ip v v)))
        (add (add (ip u u) (opp (ip v u)))
             (add (opp (ip u v)) (ip v v)))
