-- Statement-only formalization of thousand-theorems corpus artifact Q1008566
-- (thousand-theorems__agda__Q1008566), "Gauss–Lucas theorem": the zeros of
-- the derivative of a nonconstant complex polynomial lie in the real convex
-- hull of its zeros, with the indexed center-of-mass formula stated
-- explicitly. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1008566_gauss_lucas_theorem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 3 _×_

data Bottom : Set where

Not : Set → Set
Not A = A → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _×_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : Not A → Dec A

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR inverseR : R → R
    lessOrEqualR : R → R → Set
    fromNatR : Nat → R

    one-not-zero :
      oneR ≠ zeroR

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
    multiply-zero :
      (x : R) →
      multiplyR x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    inverse-zero :
      inverseR zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiplyR x (inverseR x) ≡ oneR

    order-reflexive :
      (x : R) →
      lessOrEqualR x x
    order-transitive :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR y z →
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqualR x y →
      lessOrEqualR y x →
      x ≡ y
    order-total :
      (x y : R) →
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-order :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      lessOrEqualR zeroR oneR × (zeroR ≠ oneR)

    fromNat-zero :
      fromNatR zero ≡ zeroR
    fromNat-successor :
      (n : Nat) →
      fromNatR (suc n) ≡ addR (fromNatR n) oneR
    archimedean :
      (x : R) →
      Σ Nat (λ n → lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R → Set) →
      Σ R P →
      Σ R (λ upper → (x : R) → P x → lessOrEqualR x upper) →
      Σ R
        (λ supremum →
          ((x : R) → P x → lessOrEqualR x supremum)
          ×
          ((upper : R) →
            ((x : R) → P x → lessOrEqualR x upper) →
            lessOrEqualR supremum upper))

open CompleteOrderedField

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

complexZero :
  {R : Set} →
  CompleteOrderedField R →
  Complex R
complexZero reals =
  complex (zeroR reals) (zeroR reals)

complexOne :
  {R : Set} →
  CompleteOrderedField R →
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

complexFromReal :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Complex R
complexFromReal reals x =
  complex x (zeroR reals)

complexAdd :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexAdd reals (complex a b) (complex c d) =
  complex (addR reals a c) (addR reals b d)

complexNegate :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R
complexNegate reals (complex a b) =
  complex (negateR reals a) (negateR reals b)

complexSubtract :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexSubtract reals z w =
  complexAdd reals z (complexNegate reals w)

complexMultiply :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexMultiply reals (complex a b) (complex c d) =
  complex
    (addR reals
      (multiplyR reals a c)
      (negateR reals (multiplyR reals b d)))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

complexScale :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Complex R →
  Complex R
complexScale reals scalar (complex a b) =
  complex
    (multiplyR reals scalar a)
    (multiplyR reals scalar b)

normSquared :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  R
normSquared reals (complex a b) =
  addR reals
    (multiplyR reals a a)
    (multiplyR reals b b)

divideR :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
divideR reals x y =
  multiplyR reals x (inverseR reals y)

Polynomial : Set → Set
Polynomial R = List (Complex R)

coefficient :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Nat →
  Complex R
coefficient reals [] n =
  complexZero reals
coefficient reals (a ∷ coefficients) zero =
  a
coefficient reals (a ∷ coefficients) (suc n) =
  coefficient reals coefficients n

PolynomialEqual :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Polynomial R →
  Set
PolynomialEqual reals p q =
  (n : Nat) →
  coefficient reals p n ≡ coefficient reals q n

evaluate :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Complex R →
  Complex R
evaluate reals [] z =
  complexZero reals
evaluate reals (a ∷ coefficients) z =
  complexAdd reals a
    (complexMultiply reals z (evaluate reals coefficients z))

addPolynomial :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Polynomial R →
  Polynomial R
addPolynomial reals [] q =
  q
addPolynomial reals p [] =
  p
addPolynomial reals (a ∷ p) (b ∷ q) =
  complexAdd reals a b ∷ addPolynomial reals p q

scalePolynomial :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Polynomial R →
  Polynomial R
scalePolynomial reals scalar [] =
  []
scalePolynomial reals scalar (a ∷ p) =
  complexMultiply reals scalar a ∷ scalePolynomial reals scalar p

multiplyPolynomial :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Polynomial R →
  Polynomial R
multiplyPolynomial reals [] q =
  []
multiplyPolynomial reals (a ∷ p) q =
  addPolynomial reals
    (scalePolynomial reals a q)
    (complexZero reals ∷ multiplyPolynomial reals p q)

onePolynomial :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R
onePolynomial reals =
  complexOne reals ∷ []

linearFactor :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Polynomial R
linearFactor reals z =
  complexNegate reals z ∷ complexOne reals ∷ []

powerPolynomial :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Nat →
  Polynomial R
powerPolynomial reals p zero =
  onePolynomial reals
powerPolynomial reals p (suc n) =
  multiplyPolynomial reals p (powerPolynomial reals p n)

differentiateFrom :
  {R : Set} →
  CompleteOrderedField R →
  Nat →
  Polynomial R →
  Polynomial R
differentiateFrom reals n [] =
  []
differentiateFrom reals n (a ∷ p) =
  complexScale reals (fromNatR reals n) a
  ∷ differentiateFrom reals (suc n) p

derivative :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Polynomial R
derivative reals [] =
  []
derivative reals (a ∷ p) =
  differentiateFrom reals (suc zero) p

data HasNonzeroCoefficient
  {R : Set}
  (reals : CompleteOrderedField R) :
  Polynomial R → Set where

  here :
    {a : Complex R} {p : Polynomial R} →
    a ≠ complexZero reals →
    HasNonzeroCoefficient reals (a ∷ p)

  there :
    {a : Complex R} {p : Polynomial R} →
    HasNonzeroCoefficient reals p →
    HasNonzeroCoefficient reals (a ∷ p)

Nonconstant :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Set
Nonconstant reals [] =
  Bottom
Nonconstant reals (a ∷ p) =
  HasNonzeroCoefficient reals p

PolynomialNonzero :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Set
PolynomialNonzero reals p =
  Not (PolynomialEqual reals p [])

IsRoot :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Complex R →
  Set
IsRoot reals p z =
  evaluate reals p z ≡ complexZero reals

Divides :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Polynomial R →
  Set
Divides {R} reals divisor dividend =
  Σ (Polynomial R)
    (λ quotient →
      PolynomialEqual reals dividend
        (multiplyPolynomial reals divisor quotient))

ExactRootMultiplicity :
  {R : Set} →
  CompleteOrderedField R →
  Polynomial R →
  Complex R →
  Nat →
  Set
ExactRootMultiplicity reals p z n =
  Divides reals
    (powerPolynomial reals (linearFactor reals z) n)
    p
  ×
  Not
    (Divides reals
      (powerPolynomial reals (linearFactor reals z) (suc n))
      p)

data Member {A : Set} (x : A) : List A → Set where
  at-head :
    {xs : List A} →
    Member x (x ∷ xs)
  in-tail :
    {y : A} {xs : List A} →
    Member x xs →
    Member x (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  empty :
    NoDuplicates []
  prepend :
    {x : A} {xs : List A} →
    Not (Member x xs) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

record ComplexPolynomialRootData
  (R : Set)
  (reals : CompleteOrderedField R) :
  Set₁ where

  field
    decide-complex-equality :
      (z w : Complex R) →
      Dec (z ≡ w)

    rootSupport :
      Polynomial R →
      List (Complex R)

    rootSupport-no-duplicates :
      (p : Polynomial R) →
      PolynomialNonzero reals p →
      NoDuplicates (rootSupport p)

    rootSupport-sound :
      (p : Polynomial R) →
      PolynomialNonzero reals p →
      (z : Complex R) →
      Member z (rootSupport p) →
      IsRoot reals p z

    rootSupport-complete :
      (p : Polynomial R) →
      PolynomialNonzero reals p →
      (z : Complex R) →
      IsRoot reals p z →
      Member z (rootSupport p)

    rootMultiplicity :
      Polynomial R →
      Complex R →
      Nat

    rootMultiplicity-correct :
      (p : Polynomial R) →
      PolynomialNonzero reals p →
      (z : Complex R) →
      ExactRootMultiplicity reals p z (rootMultiplicity p z)

open ComplexPolynomialRootData

singleWeight :
  {R : Set} →
  (reals : CompleteOrderedField R) →
  ComplexPolynomialRootData R reals →
  Complex R →
  Complex R →
  R
singleWeight reals roots z w
  with decide-complex-equality roots w z
... | yes equality =
  oneR reals
... | no inequality =
  zeroR reals

derivRootWeight :
  {R : Set} →
  (reals : CompleteOrderedField R) →
  (roots : ComplexPolynomialRootData R reals) →
  Polynomial R →
  Complex R →
  Complex R →
  R
derivRootWeight reals roots p z w
  with decide-complex-equality roots
    (evaluate reals p z)
    (complexZero reals)
... | yes evaluation-is-zero =
  singleWeight reals roots z w
... | no evaluation-is-nonzero =
  divideR reals
    (fromNatR reals (rootMultiplicity roots p w))
    (normSquared reals (complexSubtract reals z w))

sumWeights :
  {R : Set} →
  CompleteOrderedField R →
  List R →
  R
sumWeights reals [] =
  zeroR reals
sumWeights reals (weight ∷ weights) =
  addR reals weight (sumWeights reals weights)

weightsOn :
  {R : Set} →
  (Complex R → R) →
  List (Complex R) →
  List R
weightsOn weight [] =
  []
weightsOn weight (z ∷ points) =
  weight z ∷ weightsOn weight points

weightedSum :
  {R : Set} →
  CompleteOrderedField R →
  List (Complex R) →
  List R →
  Complex R
weightedSum reals [] weights =
  complexZero reals
weightedSum reals points [] =
  complexZero reals
weightedSum reals (z ∷ points) (weight ∷ weights) =
  complexAdd reals
    (complexScale reals weight z)
    (weightedSum reals points weights)

centerMass :
  {R : Set} →
  CompleteOrderedField R →
  List (Complex R) →
  (Complex R → R) →
  Complex R
centerMass reals points weight =
  complexScale reals
    (inverseR reals (sumWeights reals (weightsOn weight points)))
    (weightedSum reals points (weightsOn weight points))

data ConvexTerms
  {R : Set}
  (reals : CompleteOrderedField R)
  (S : Complex R → Set) :
  List (Complex R) →
  List R →
  Set where

  no-terms :
    ConvexTerms reals S [] []

  add-term :
    {z : Complex R} {points : List (Complex R)}
    {weight : R} {weights : List R} →
    S z →
    lessOrEqualR reals (zeroR reals) weight →
    ConvexTerms reals S points weights →
    ConvexTerms reals S (z ∷ points) (weight ∷ weights)

ConvexHull :
  {R : Set} →
  CompleteOrderedField R →
  (Complex R → Set) →
  Complex R →
  Set
ConvexHull {R} reals S z =
  Σ (List (Complex R))
    (λ points →
      Σ (List R)
        (λ weights →
          ConvexTerms reals S points weights
          ×
          ((sumWeights reals weights ≡ oneR reals)
          ×
          (weightedSum reals points weights ≡ z))))

eq-centerMass-of-eval-derivative-eq-zero : Set₁
eq-centerMass-of-eval-derivative-eq-zero =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  (roots : ComplexPolynomialRootData R reals) →
  (p : Polynomial R) →
  Nonconstant reals p →
  (z : Complex R) →
  IsRoot reals (derivative reals p) z →
  z ≡
    centerMass reals
      (rootSupport roots p)
      (derivRootWeight reals roots p z)

rootSet-derivative-subset-convexHull-rootSet : Set₁
rootSet-derivative-subset-convexHull-rootSet =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  (p : Polynomial R) →
  Nonconstant reals p →
  (z : Complex R) →
  IsRoot reals (derivative reals p) z →
  ConvexHull reals (IsRoot reals p) z

gauss-lucas-theorem : Set₁
gauss-lucas-theorem =
  eq-centerMass-of-eval-derivative-eq-zero
  ×
  rootSet-derivative-subset-convexHull-rootSet
