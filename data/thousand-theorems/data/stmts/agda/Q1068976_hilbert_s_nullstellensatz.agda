-- Statement-only formalization of thousand-theorems corpus artifact Q1068976,
-- "Hilbert's Nullstellensatz": over an algebraically closed field extension,
-- the ideal vanishing on the common zero locus of a polynomial ideal in
-- finitely many variables is its radical. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1068976_hilbert_s_nullstellensatz where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)

infix 4 _≠_ _↔_

data Bottom : Set where

Not :
  {a : Level} →
  Set a →
  Set a
Not A =
  A → Bottom

_≠_ :
  {a : Level} →
  {A : Set a} →
  A →
  A →
  Set a
x ≠ y =
  Not (x ≡ y)

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A → B
    backward : B → A

data Dec
  {a : Level}
  (A : Set a) :
  Set a where

  yes : A → Dec A
  no  : Not A → Dec A

cong :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl =
  refl

subst :
  {a b : Level} →
  {A : Set a} →
  (P : A → Set b) →
  {x y : A} →
  x ≡ y →
  P x →
  P y
subst P refl px =
  px

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

Finite :
  {a : Level} →
  Set a →
  Set a
Finite A =
  Σ Nat (λ cardinality → Bijection A (Fin cardinality))

record CommutativeRing
  {a : Level}
  (R : Set a) :
  Set a where

  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR : R → R

    add-commutative :
      (x y : R) →
      addR x y ≡ addR y x
    add-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-zero :
      (x : R) →
      addR x zeroR ≡ x
    add-inverse :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) →
      multiplyR x oneR ≡ x
    distribute :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)

record Field
  {a : Level}
  (F : Set a) :
  Set a where

  field
    ring : CommutativeRing F
    inverseF : F → F
    one-not-zero :
      CommutativeRing.oneR ring ≠
      CommutativeRing.zeroR ring
    multiply-inverse :
      (x : F) →
      x ≠ CommutativeRing.zeroR ring →
      CommutativeRing.multiplyR ring x (inverseF x) ≡
      CommutativeRing.oneR ring

record RingHom
  {a b : Level}
  {R : Set a}
  {S : Set b}
  (domain : CommutativeRing R)
  (codomain : CommutativeRing S) :
  Set (a ⊔ b) where

  field
    map : R → S
    map-zero :
      map (CommutativeRing.zeroR domain) ≡
      CommutativeRing.zeroR codomain
    map-one :
      map (CommutativeRing.oneR domain) ≡
      CommutativeRing.oneR codomain
    map-add :
      (x y : R) →
      map (CommutativeRing.addR domain x y) ≡
      CommutativeRing.addR codomain (map x) (map y)
    map-multiply :
      (x y : R) →
      map (CommutativeRing.multiplyR domain x y) ≡
      CommutativeRing.multiplyR codomain (map x) (map y)

power :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  R →
  Nat →
  R
power ring x zero =
  CommutativeRing.oneR ring
power ring x (suc n) =
  CommutativeRing.multiplyR ring x (power ring x n)

evaluateUnivariate :
  {a : Level} →
  {F : Set a} →
  CommutativeRing F →
  List F →
  F →
  F
evaluateUnivariate ring [] x =
  CommutativeRing.zeroR ring
evaluateUnivariate ring (coefficient ∷ coefficients) x =
  CommutativeRing.addR ring coefficient
    (CommutativeRing.multiplyR ring x
      (evaluateUnivariate ring coefficients x))

data HasNonzeroCoefficient
  {a : Level}
  {F : Set a}
  (ring : CommutativeRing F) :
  List F →
  Set a where

  here :
    {coefficient : F}
    {coefficients : List F} →
    coefficient ≠ CommutativeRing.zeroR ring →
    HasNonzeroCoefficient ring (coefficient ∷ coefficients)

  there :
    {coefficient : F}
    {coefficients : List F} →
    HasNonzeroCoefficient ring coefficients →
    HasNonzeroCoefficient ring (coefficient ∷ coefficients)

data Nonconstant
  {a : Level}
  {F : Set a}
  (ring : CommutativeRing F) :
  List F →
  Set a where

  nonconstant :
    {constant : F}
    {higher-coefficients : List F} →
    HasNonzeroCoefficient ring higher-coefficients →
    Nonconstant ring (constant ∷ higher-coefficients)

AlgebraicallyClosed :
  {a : Level} →
  {F : Set a} →
  Field F →
  Set a
AlgebraicallyClosed field-structure =
  (coefficients : List _) →
  Nonconstant (Field.ring field-structure) coefficients →
  Σ _
    (λ root →
      evaluateUnivariate
        (Field.ring field-structure)
        coefficients
        root
      ≡
      CommutativeRing.zeroR (Field.ring field-structure))

record Monomial
  {s : Level}
  (σ : Set s) :
  Set s where

  constructor monomial
  field
    exponent : σ → Nat

record Term
  {a s : Level}
  (k : Set a)
  (σ : Set s) :
  Set (a ⊔ s) where

  constructor term
  field
    coefficient : k
    monomial-part : Monomial σ

Polynomial :
  {a s : Level} →
  Set a →
  Set s →
  Set (a ⊔ s)
Polynomial k σ =
  List (Term k σ)

decideNatEquality :
  (m n : Nat) →
  Dec (m ≡ n)
decideNatEquality zero zero =
  yes refl
decideNatEquality zero (suc n) =
  no (λ ())
decideNatEquality (suc m) zero =
  no (λ ())
decideNatEquality (suc m) (suc n) with decideNatEquality m n
... | yes equality =
  yes (cong suc equality)
... | no inequality =
  no (λ { refl → inequality refl })

decideFinFunctionEquality :
  (n : Nat) →
  (f g : Fin n → Nat) →
  Dec ((i : Fin n) → f i ≡ g i)
decideFinFunctionEquality zero f g =
  yes (λ ())
decideFinFunctionEquality (suc n) f g
  with decideNatEquality (f fzero) (g fzero)
... | no unequal-at-zero =
  no (λ equality → unequal-at-zero (equality fzero))
... | yes equal-at-zero
  with decideFinFunctionEquality n
    (λ i → f (fsuc i))
    (λ i → g (fsuc i))
... | no unequal-later =
  no (λ equality → unequal-later (λ i → equality (fsuc i)))
... | yes equal-later =
  yes λ
    { fzero    → equal-at-zero
    ; (fsuc i) → equal-later i
    }

MonomialEqual :
  {s : Level} →
  {σ : Set s} →
  Monomial σ →
  Monomial σ →
  Set s
MonomialEqual left right =
  (x : _) →
  Monomial.exponent left x ≡
  Monomial.exponent right x

decideMonomialEquality :
  {s : Level} →
  {σ : Set s} →
  Finite σ →
  (left right : Monomial σ) →
  Dec (MonomialEqual left right)
decideMonomialEquality (cardinality , enumeration) left right
  with decideFinFunctionEquality cardinality
    (λ i →
      Monomial.exponent left
        (Bijection.from enumeration i))
    (λ i →
      Monomial.exponent right
        (Bijection.from enumeration i))
... | no inequality =
  no
    (λ equality →
      inequality
        (λ i →
          equality (Bijection.from enumeration i)))
... | yes equality =
  yes
    (λ x →
      subst
        (λ y →
          Monomial.exponent left y ≡
          Monomial.exponent right y)
        (Bijection.from-to enumeration x)
        (equality (Bijection.to enumeration x)))

append :
  {a : Level} →
  {A : Set a} →
  List A →
  List A →
  List A
append [] ys =
  ys
append (x ∷ xs) ys =
  x ∷ append xs ys

addMonomial :
  {s : Level} →
  {σ : Set s} →
  Monomial σ →
  Monomial σ →
  Monomial σ
addMonomial left right =
  monomial
    (λ x →
      Monomial.exponent left x +
      Monomial.exponent right x)

multiplyTerms :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  CommutativeRing k →
  Term k σ →
  Term k σ →
  Term k σ
multiplyTerms ring left right =
  term
    (CommutativeRing.multiplyR ring
      (Term.coefficient left)
      (Term.coefficient right))
    (addMonomial
      (Term.monomial-part left)
      (Term.monomial-part right))

multiplyByTerm :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  CommutativeRing k →
  Term k σ →
  Polynomial k σ →
  Polynomial k σ
multiplyByTerm ring left [] =
  []
multiplyByTerm ring left (right ∷ rest) =
  multiplyTerms ring left right ∷
  multiplyByTerm ring left rest

addPolynomial :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  Polynomial k σ →
  Polynomial k σ →
  Polynomial k σ
addPolynomial =
  append

multiplyPolynomial :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  CommutativeRing k →
  Polynomial k σ →
  Polynomial k σ →
  Polynomial k σ
multiplyPolynomial ring [] right =
  []
multiplyPolynomial ring (left ∷ rest) right =
  append
    (multiplyByTerm ring left right)
    (multiplyPolynomial ring rest right)

zeroMonomial :
  {s : Level} →
  {σ : Set s} →
  Monomial σ
zeroMonomial =
  monomial (λ _ → zero)

onePolynomial :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  CommutativeRing k →
  Polynomial k σ
onePolynomial ring =
  term (CommutativeRing.oneR ring) zeroMonomial ∷ []

powerPolynomial :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  CommutativeRing k →
  Polynomial k σ →
  Nat →
  Polynomial k σ
powerPolynomial ring polynomial zero =
  onePolynomial ring
powerPolynomial ring polynomial (suc n) =
  multiplyPolynomial ring polynomial
    (powerPolynomial ring polynomial n)

coefficientAt :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  CommutativeRing k →
  Finite σ →
  Polynomial k σ →
  Monomial σ →
  k
coefficientAt ring finite [] target =
  CommutativeRing.zeroR ring
coefficientAt ring finite (summand ∷ rest) target
  with decideMonomialEquality finite
    (Term.monomial-part summand)
    target
... | yes equal =
  CommutativeRing.addR ring
    (Term.coefficient summand)
    (coefficientAt ring finite rest target)
... | no unequal =
  coefficientAt ring finite rest target

PolynomialEqual :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  CommutativeRing k →
  Finite σ →
  Polynomial k σ →
  Polynomial k σ →
  Set (a ⊔ s)
PolynomialEqual ring finite left right =
  (monomial-part : Monomial _) →
  coefficientAt ring finite left monomial-part ≡
  coefficientAt ring finite right monomial-part

record PolynomialIdeal
  {a s : Level}
  {k : Set a}
  {σ : Set s}
  (ring : CommutativeRing k)
  (finite : Finite σ) :
  Set (lsuc (a ⊔ s)) where

  field
    member :
      Polynomial k σ →
      Set (a ⊔ s)
    membership-propositional :
      (polynomial : Polynomial k σ) →
      (u v : member polynomial) →
      u ≡ v
    respects-polynomial-equality :
      (left right : Polynomial k σ) →
      PolynomialEqual ring finite left right →
      member left →
      member right
    contains-zero :
      member []
    closed-under-addition :
      (left right : Polynomial k σ) →
      member left →
      member right →
      member (addPolynomial left right)
    absorbs-multiplication :
      (left right : Polynomial k σ) →
      member left →
      member (multiplyPolynomial ring left right)

productFin :
  {a : Level} →
  {R : Set a} →
  CommutativeRing R →
  (n : Nat) →
  (Fin n → R) →
  R
productFin ring zero values =
  CommutativeRing.oneR ring
productFin ring (suc n) values =
  CommutativeRing.multiplyR ring
    (values fzero)
    (productFin ring n (λ i → values (fsuc i)))

evaluateMonomial :
  {b s : Level} →
  {K : Set b} →
  {σ : Set s} →
  CommutativeRing K →
  Finite σ →
  (σ → K) →
  Monomial σ →
  K
evaluateMonomial ring (cardinality , enumeration) point monomial-part =
  productFin ring cardinality
    (λ i →
      power ring
        (point (Bijection.from enumeration i))
        (Monomial.exponent monomial-part
          (Bijection.from enumeration i)))

evaluateTerm :
  {a b s : Level} →
  {k : Set a} →
  {K : Set b} →
  {σ : Set s} →
  (base : CommutativeRing k) →
  (extension : CommutativeRing K) →
  RingHom base extension →
  Finite σ →
  (σ → K) →
  Term k σ →
  K
evaluateTerm base extension algebra-map finite point summand =
  CommutativeRing.multiplyR extension
    (RingHom.map algebra-map (Term.coefficient summand))
    (evaluateMonomial extension finite point
      (Term.monomial-part summand))

evaluatePolynomial :
  {a b s : Level} →
  {k : Set a} →
  {K : Set b} →
  {σ : Set s} →
  (base : CommutativeRing k) →
  (extension : CommutativeRing K) →
  RingHom base extension →
  Finite σ →
  Polynomial k σ →
  (σ → K) →
  K
evaluatePolynomial base extension algebra-map finite [] point =
  CommutativeRing.zeroR extension
evaluatePolynomial base extension algebra-map finite
  (summand ∷ rest) point =
  CommutativeRing.addR extension
    (evaluateTerm base extension algebra-map finite point summand)
    (evaluatePolynomial base extension algebra-map finite rest point)

ZeroLocus :
  {a b s : Level} →
  {k : Set a} →
  {K : Set b} →
  {σ : Set s} →
  (base : CommutativeRing k) →
  (extension : CommutativeRing K) →
  RingHom base extension →
  (finite : Finite σ) →
  PolynomialIdeal base finite →
  (σ → K) →
  Set (a ⊔ b ⊔ s)
ZeroLocus base extension algebra-map finite ideal point =
  (polynomial : Polynomial _ _) →
  PolynomialIdeal.member ideal polynomial →
  evaluatePolynomial
    base extension algebra-map finite polynomial point
  ≡
  CommutativeRing.zeroR extension

VanishesOnZeroLocus :
  {a b s : Level} →
  {k : Set a} →
  {K : Set b} →
  {σ : Set s} →
  (base : CommutativeRing k) →
  (extension : CommutativeRing K) →
  RingHom base extension →
  (finite : Finite σ) →
  PolynomialIdeal base finite →
  Polynomial k σ →
  Set (a ⊔ b ⊔ s)
VanishesOnZeroLocus base extension algebra-map finite ideal polynomial =
  (point : _ → _) →
  ZeroLocus base extension algebra-map finite ideal point →
  evaluatePolynomial
    base extension algebra-map finite polynomial point
  ≡
  CommutativeRing.zeroR extension

RadicalMember :
  {a s : Level} →
  {k : Set a} →
  {σ : Set s} →
  (ring : CommutativeRing k) →
  (finite : Finite σ) →
  PolynomialIdeal ring finite →
  Polynomial k σ →
  Set (a ⊔ s)
RadicalMember ring finite ideal polynomial =
  Σ Nat
    (λ exponent →
      PolynomialIdeal.member ideal
        (powerPolynomial ring polynomial exponent))

-- Lean: MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
hilbert-s-nullstellensatz :
  (a b s : Level) →
  Set (lsuc (a ⊔ b ⊔ s))
hilbert-s-nullstellensatz a b s =
  (k : Set a) →
  (K : Set b) →
  (σ : Set s) →
  (base-field : Field k) →
  (extension-field : Field K) →
  (algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)) →
  AlgebraicallyClosed extension-field →
  (finite : Finite σ) →
  (ideal :
    PolynomialIdeal
      (Field.ring base-field)
      finite) →
  (polynomial : Polynomial k σ) →
  VanishesOnZeroLocus
    (Field.ring base-field)
    (Field.ring extension-field)
    algebra-map
    finite
    ideal
    polynomial
  ↔
  RadicalMember
    (Field.ring base-field)
    finite
    ideal
    polynomial
