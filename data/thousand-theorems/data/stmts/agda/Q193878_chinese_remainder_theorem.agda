-- Statement-only formalization of thousand-theorems corpus artifact Q193878,
-- "Chinese remainder theorem": pairwise coprime ideals in a commutative ring
-- give a canonical ring isomorphism from the quotient by their intersection
-- to the product of the individual quotient rings. This file contains no proof.

{-# OPTIONS --safe #-}

module Q193878_chinese_remainder_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 4 _×_
infix 4 _≠_

data Bottom {a : Level} : Set a where

_≠_ :
  {a : Level} →
  {A : Set a} →
  A →
  A →
  Set a
_≠_ {a} x y =
  x ≡ y → Bottom {a}

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor _,_
  field
    first  : A
    second : B

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size       : Nat
    equivalence : Bijection A (Fin size)

record CommutativeRing
  {r : Level}
  (R : Set r) :
  Set r where

  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR : R → R

    add-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-commutative :
      (x y : R) →
      addR x y ≡ addR y x
    add-zero-left :
      (x : R) →
      addR zeroR x ≡ x
    add-zero-right :
      (x : R) →
      addR x zeroR ≡ x
    add-inverse-left :
      (x : R) →
      addR (negateR x) x ≡ zeroR
    add-inverse-right :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiply-one-left :
      (x : R) →
      multiplyR oneR x ≡ x
    multiply-one-right :
      (x : R) →
      multiplyR x oneR ≡ x
    distribute-left :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) →
      multiplyR (addR x y) z ≡
      addR (multiplyR x z) (multiplyR y z)

record Ideal
  {r : Level}
  {R : Set r}
  (ring : CommutativeRing R) :
  Set (lsuc r) where

  field
    member : R → Set r
    membership-propositional :
      (x : R) →
      (u v : member x) →
      u ≡ v
    contains-zero :
      member (CommutativeRing.zeroR ring)
    closed-under-addition :
      (x y : R) →
      member x →
      member y →
      member (CommutativeRing.addR ring x y)
    closed-under-negation :
      (x : R) →
      member x →
      member (CommutativeRing.negateR ring x)
    absorbs-multiplication :
      (a x : R) →
      member x →
      member (CommutativeRing.multiplyR ring a x)

difference :
  {r : Level} →
  {R : Set r} →
  CommutativeRing R →
  R →
  R →
  R
difference ring x y =
  CommutativeRing.addR ring x
    (CommutativeRing.negateR ring y)

IsCoprime :
  {r : Level} →
  {R : Set r} →
  {ring : CommutativeRing R} →
  Ideal ring →
  Ideal ring →
  Set r
IsCoprime {R = R} {ring = ring} left-ideal right-ideal =
  Σ R
    (λ x →
      Ideal.member left-ideal x ×
      Σ R
        (λ y →
          Ideal.member right-ideal y ×
          (CommutativeRing.addR ring x y ≡
           CommutativeRing.oneR ring)))

PairwiseCoprime :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  {ring : CommutativeRing R} →
  (Index → Ideal ring) →
  Set (r ⊔ i)
PairwiseCoprime ideals =
  (i j : _) →
  i ≠ j →
  IsCoprime (ideals i) (ideals j)

IntersectionQuotientRelated :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  (ring : CommutativeRing R) →
  (ideals : Index → Ideal ring) →
  R →
  R →
  Set (r ⊔ i)
IntersectionQuotientRelated ring ideals x y =
  (i : _) →
  Ideal.member (ideals i) (difference ring x y)

ProductQuotientRelated :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  (ring : CommutativeRing R) →
  (ideals : Index → Ideal ring) →
  (Index → R) →
  (Index → R) →
  Set (r ⊔ i)
ProductQuotientRelated ring ideals f g =
  (i : _) →
  Ideal.member (ideals i) (difference ring (f i) (g i))

constantFamily :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  R →
  Index →
  R
constantFamily x _ =
  x

pointwiseZero :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  CommutativeRing R →
  Index →
  R
pointwiseZero ring _ =
  CommutativeRing.zeroR ring

pointwiseOne :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  CommutativeRing R →
  Index →
  R
pointwiseOne ring _ =
  CommutativeRing.oneR ring

pointwiseAdd :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  CommutativeRing R →
  (Index → R) →
  (Index → R) →
  Index →
  R
pointwiseAdd ring f g i =
  CommutativeRing.addR ring (f i) (g i)

pointwiseMultiply :
  {r i : Level} →
  {R : Set r} →
  {Index : Set i} →
  CommutativeRing R →
  (Index → R) →
  (Index → R) →
  Index →
  R
pointwiseMultiply ring f g i =
  CommutativeRing.multiplyR ring (f i) (g i)

record QuotientRingEquiv
  {a b p q : Level}
  (A : Set a)
  (B : Set b)
  (domain-related : A → A → Set p)
  (codomain-related : B → B → Set q)
  (domain-zero domain-one : A)
  (domain-add domain-multiply : A → A → A)
  (codomain-zero codomain-one : B)
  (codomain-add codomain-multiply : B → B → B)
  (forward : A → B) :
  Set (a ⊔ b ⊔ p ⊔ q) where

  field
    inverse :
      B → A
    forward-congruent :
      (x y : A) →
      domain-related x y →
      codomain-related (forward x) (forward y)
    inverse-congruent :
      (x y : B) →
      codomain-related x y →
      domain-related (inverse x) (inverse y)
    map-zero :
      codomain-related (forward domain-zero) codomain-zero
    map-one :
      codomain-related (forward domain-one) codomain-one
    map-add :
      (x y : A) →
      codomain-related
        (forward (domain-add x y))
        (codomain-add (forward x) (forward y))
    map-multiply :
      (x y : A) →
      codomain-related
        (forward (domain-multiply x y))
        (codomain-multiply (forward x) (forward y))
    inverse-forward :
      (x : A) →
      domain-related (inverse (forward x)) x
    forward-inverse :
      (y : B) →
      codomain-related (forward (inverse y)) y

-- Lean: Ideal.quotientInfRingEquivPiQuotient
chinese-remainder-theorem :
  (r i : Level) →
  Set (lsuc (r ⊔ i))
chinese-remainder-theorem r i =
  {R : Set r} →
  {Index : Set i} →
  (ring : CommutativeRing R) →
  (finite-index : Finite Index) →
  (ideals : Index → Ideal ring) →
  PairwiseCoprime ideals →
  QuotientRingEquiv
    R
    (Index → R)
    (IntersectionQuotientRelated ring ideals)
    (ProductQuotientRelated ring ideals)
    (CommutativeRing.zeroR ring)
    (CommutativeRing.oneR ring)
    (CommutativeRing.addR ring)
    (CommutativeRing.multiplyR ring)
    (pointwiseZero ring)
    (pointwiseOne ring)
    (pointwiseAdd ring)
    (pointwiseMultiply ring)
    constantFamily
