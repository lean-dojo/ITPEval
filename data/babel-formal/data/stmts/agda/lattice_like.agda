-- Statement-only formalization of the Babel-formal topic lattice_like. This file contains no
-- proof.

module lattice_like where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

record LatticeLike {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    le  : A → A → Set ℓ
    inf : A → A → A
    sup : A → A → A

    le-refl    : (x : A) → le x x
    le-trans   : (x y z : A) → le x y → le y z → le x z
    le-antisym : (x y : A) → le x y → le y x → x ≡ y

    le-inf-left  : (a b : A) → le (inf a b) a
    le-inf-right : (a b : A) → le (inf a b) b
    le-inf-intro :
      (c a b : A) → le c a → le c b → le c (inf a b)

    le-sup-left  : (a b : A) → le a (sup a b)
    le-sup-right : (a b : A) → le b (sup a b)
    sup-le-intro :
      (a b c : A) → le a c → le b c → le (sup a b) c

module LatticeLikeStatements
  {ℓ : Level} {A : Set ℓ} (L : LatticeLike A) where

  open LatticeLike L

  inf-comm : Set ℓ
  inf-comm =
    (a b : A) → inf a b ≡ inf b a

  sup-comm : Set ℓ
  sup-comm =
    (a b : A) → sup a b ≡ sup b a

  inf-assoc : Set ℓ
  inf-assoc =
    (a b c : A) → inf (inf a b) c ≡ inf a (inf b c)

  sup-assoc : Set ℓ
  sup-assoc =
    (a b c : A) → sup (sup a b) c ≡ sup a (sup b c)

  inf-absorption : Set ℓ
  inf-absorption =
    (a b : A) → inf a (sup a b) ≡ a

  sup-absorption : Set ℓ
  sup-absorption =
    (a b : A) → sup a (inf a b) ≡ a
