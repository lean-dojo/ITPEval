-- Statement-only formalization of thousand-theorems corpus artifact Q4830725,
-- "Ax-Grothendieck theorem": over an algebraically closed field, an injective
-- polynomial self-map of the zero locus of a multivariate polynomial ideal in
-- finitely many variables is surjective on that zero locus. This file contains no proof.

{-# OPTIONS --safe #-}

module Q4830725_ax_grothendieck_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)

infix 4 _≠_
infixr 4 _×_

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

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

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
  (K : Set a)
  (σ : Set s) :
  Set (a ⊔ s) where

  constructor term
  field
    coefficient   : K
    monomial-part : Monomial σ

Polynomial :
  {a s : Level} →
  Set a →
  Set s →
  Set (a ⊔ s)
Polynomial K σ =
  List (Term K σ)

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
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Term K σ →
  Term K σ →
  Term K σ
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
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Term K σ →
  Polynomial K σ →
  Polynomial K σ
multiplyByTerm ring left [] =
  []
multiplyByTerm ring left (right ∷ rest) =
  multiplyTerms ring left right ∷
  multiplyByTerm ring left rest

addPolynomial :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  Polynomial K σ →
  Polynomial K σ →
  Polynomial K σ
addPolynomial =
  append

negatePolynomial :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Polynomial K σ →
  Polynomial K σ
negatePolynomial ring [] =
  []
negatePolynomial ring (summand ∷ rest) =
  term
    (CommutativeRing.negateR ring
      (Term.coefficient summand))
    (Term.monomial-part summand)
  ∷ negatePolynomial ring rest

multiplyPolynomial :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Polynomial K σ →
  Polynomial K σ →
  Polynomial K σ
multiplyPolynomial ring [] right =
  []
multiplyPolynomial ring (left ∷ rest) right =
  append
    (multiplyByTerm ring left right)
    (multiplyPolynomial ring rest right)

coefficientAt :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Finite σ →
  Polynomial K σ →
  Monomial σ →
  K
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
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Finite σ →
  Polynomial K σ →
  Polynomial K σ →
  Set (a ⊔ s)
PolynomialEqual ring finite left right =
  (monomial-part : Monomial _) →
  coefficientAt ring finite left monomial-part ≡
  coefficientAt ring finite right monomial-part

record PolynomialIdeal
  {a s : Level}
  {K : Set a}
  {σ : Set s}
  (ring : CommutativeRing K)
  (finite : Finite σ) :
  Set (lsuc (a ⊔ s)) where

  field
    member :
      Polynomial K σ →
      Set (a ⊔ s)
    membership-propositional :
      (polynomial : Polynomial K σ) →
      (u v : member polynomial) →
      u ≡ v
    respects-polynomial-equality :
      (left right : Polynomial K σ) →
      PolynomialEqual ring finite left right →
      member left →
      member right
    contains-zero :
      member []
    closed-under-addition :
      (left right : Polynomial K σ) →
      member left →
      member right →
      member (addPolynomial left right)
    closed-under-negation :
      (polynomial : Polynomial K σ) →
      member polynomial →
      member (negatePolynomial ring polynomial)
    absorbs-multiplication :
      (left right : Polynomial K σ) →
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
  {a s : Level} →
  {K : Set a} →
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
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Finite σ →
  (σ → K) →
  Term K σ →
  K
evaluateTerm ring finite point summand =
  CommutativeRing.multiplyR ring
    (Term.coefficient summand)
    (evaluateMonomial ring finite point
      (Term.monomial-part summand))

evaluatePolynomial :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Finite σ →
  Polynomial K σ →
  (σ → K) →
  K
evaluatePolynomial ring finite [] point =
  CommutativeRing.zeroR ring
evaluatePolynomial ring finite (summand ∷ rest) point =
  CommutativeRing.addR ring
    (evaluateTerm ring finite point summand)
    (evaluatePolynomial ring finite rest point)

ZeroLocus :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  (ring : CommutativeRing K) →
  (finite : Finite σ) →
  PolynomialIdeal ring finite →
  (σ → K) →
  Set (a ⊔ s)
ZeroLocus ring finite ideal point =
  (polynomial : Polynomial _ _) →
  PolynomialIdeal.member ideal polynomial →
  evaluatePolynomial ring finite polynomial point ≡
  CommutativeRing.zeroR ring

PolynomialMap :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  CommutativeRing K →
  Finite σ →
  (σ → Polynomial K σ) →
  (σ → K) →
  σ →
  K
PolynomialMap ring finite polynomials point coordinate =
  evaluatePolynomial ring finite (polynomials coordinate) point

PointwiseEqual :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  (A → B) →
  Set (a ⊔ b)
PointwiseEqual left right =
  (x : _) →
  left x ≡ right x

MapsTo :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  ((σ → K) → Set (a ⊔ s)) →
  ((σ → K) → (σ → K)) →
  Set (a ⊔ s)
MapsTo subset function =
  (x : _) →
  subset x →
  subset (function x)

InjectiveOn :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  ((σ → K) → Set (a ⊔ s)) →
  ((σ → K) → (σ → K)) →
  Set (a ⊔ s)
InjectiveOn subset function =
  (x y : _) →
  subset x →
  subset y →
  PointwiseEqual (function x) (function y) →
  PointwiseEqual x y

SurjectiveOn :
  {a s : Level} →
  {K : Set a} →
  {σ : Set s} →
  ((σ → K) → Set (a ⊔ s)) →
  ((σ → K) → (σ → K)) →
  Set (a ⊔ s)
SurjectiveOn subset function =
  (y : _) →
  subset y →
  Σ _
    (λ x →
      subset x ×
      PointwiseEqual (function x) y)

-- Lean: ax_grothendieck_zeroLocus
ax-grothendieck-zero-locus :
  (a s : Level) →
  Set (lsuc (a ⊔ s))
ax-grothendieck-zero-locus a s =
  (K : Set a) →
  (σ : Set s) →
  (field-structure : Field K) →
  AlgebraicallyClosed field-structure →
  (finite : Finite σ) →
  (ideal :
    PolynomialIdeal
      (Field.ring field-structure)
      finite) →
  (polynomials : σ → Polynomial K σ) →
  let
    locus =
      ZeroLocus
        (Field.ring field-structure)
        finite
        ideal
    polynomial-map =
      PolynomialMap
        (Field.ring field-structure)
        finite
        polynomials
  in
  MapsTo locus polynomial-map →
  InjectiveOn locus polynomial-map →
  SurjectiveOn locus polynomial-map
