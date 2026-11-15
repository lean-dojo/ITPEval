-- Statement-only formalization of "Minkowski's Fundamental Theorem" from Hundred Theorems item
-- 040. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤ₙ_ _<ₙ_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤ₙ_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ₙ n
  suc≤suc : {m n : Nat} → m ≤ₙ n → suc m ≤ₙ suc n

_<ₙ_ : Nat → Nat → Set
m <ₙ n = suc m ≤ₙ n

data PositiveDimension : Nat → Set where
  positive : {n : Nat} → PositiveDimension (suc n)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessThan : R → R → Set
    fromNat : Nat → R

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) → add x y ≡ add y x
    add-associative :
      (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : R) → add x zeroR ≡ x
    add-inverse :
      (x : R) → add x (negate x) ≡ zeroR
    negate-involutive :
      (x : R) → negate (negate x) ≡ x

    multiply-commutative :
      (x y : R) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : R) → multiply x oneR ≡ x
    multiply-zero :
      (x : R) → multiply x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (inverse x) ≡ oneR

    order-irreflexive :
      (x : R) →
      lessThan x x →
      ⊥
    order-transitive :
      (x y z : R) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : R) →
      lessThan x y ∨
      (x ≡ y ∨ lessThan y x)
    add-order :
      (x y z : R) →
      lessThan x y →
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      lessThan zeroR (multiply x y)
    zero-less-than-one :
      lessThan zeroR oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) →
      fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) →
      fromNat (m + n) ≡
      add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡
      multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) →
      fromNat m ≡ fromNat n →
      m ≡ n

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessThan x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) →
          P x →
          lessThan x upper ∨ x ≡ upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            P x →
            lessThan x supremum ∨ x ≡ supremum) ∧
          ((upper : R) →
            ((x : R) →
              P x →
              lessThan x upper ∨ x ≡ upper) →
            lessThan supremum upper ∨ supremum ≡ upper))

open CompleteOrderedField

LessOrEqual :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  Set
LessOrEqual reals x y =
  lessThan reals x y ∨ x ≡ y

subtract :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
subtract reals x y =
  add reals x (negate reals y)

fromInt :
  {R : Set} →
  CompleteOrderedField R →
  Int →
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

power :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Nat →
  R
power reals x zero =
  oneR reals
power reals x (suc n) =
  multiply reals x (power reals x n)

twoPower :
  {R : Set} →
  CompleteOrderedField R →
  Nat →
  R
twoPower reals n =
  power reals
    (add reals (oneR reals) (oneR reals))
    n

Vector : Set → Nat → Set
Vector R n = Fin n → R

Region : Set → Nat → Set₁
Region R n = Vector R n → Set

zeroVector :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Vector R n
zeroVector reals _ =
  zeroR reals

addVector :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Vector R n →
  Vector R n →
  Vector R n
addVector reals x y i =
  add reals (x i) (y i)

negateVector :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Vector R n →
  Vector R n
negateVector reals x i =
  negate reals (x i)

subtractVector :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Vector R n →
  Vector R n →
  Vector R n
subtractVector reals x y =
  addVector reals x (negateVector reals y)

scaleVector :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  R →
  Vector R n →
  Vector R n
scaleVector reals scalar x i =
  multiply reals scalar (x i)

linearCombination :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  R →
  Vector R n →
  Vector R n →
  Vector R n
linearCombination reals t x y =
  addVector reals
    (scaleVector reals t x)
    (scaleVector reals
      (subtract reals (oneR reals) t)
      y)

Convex :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Region R n →
  Set
Convex {R} {n} reals body =
  (x y : Vector R n) →
  body x →
  body y →
  (t : R) →
  LessOrEqual reals (zeroR reals) t →
  LessOrEqual reals t (oneR reals) →
  body (linearCombination reals t x y)

OriginSymmetric :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Region R n →
  Set
OriginSymmetric {R} {n} reals body =
  (x : Vector R n) →
  body x →
  body (negateVector reals x)

IntegerCoordinate :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
IntegerCoordinate reals x =
  Exists Int (λ z → x ≡ fromInt reals z)

IntegerVector :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Vector R n →
  Set
IntegerVector {n = n} reals x =
  (i : Fin n) →
  IntegerCoordinate reals (x i)

DistinctVectors :
  {R : Set} →
  {n : Nat} →
  Vector R n →
  Vector R n →
  Set
DistinctVectors {n = n} x y =
  Exists (Fin n) (λ i → x i ≠ y i)

NonzeroVector :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Vector R n →
  Set
NonzeroVector {n = n} reals x =
  Exists (Fin n) (λ i → x i ≠ zeroR reals)

ConvergesTo :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  R →
  Set
ConvergesTo reals sequence limit =
  (epsilon : _) →
  lessThan reals (zeroR reals) epsilon →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      lessThan reals
        (subtract reals limit epsilon)
        (sequence n) ∧
      lessThan reals
        (sequence n)
        (add reals limit epsilon))

VectorConvergesTo :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  (Nat → Vector R n) →
  Vector R n →
  Set
VectorConvergesTo {n = n} reals sequence limit =
  (i : Fin n) →
  ConvergesTo reals
    (λ k → sequence k i)
    (limit i)

StrictlyIncreasing : (Nat → Nat) → Set
StrictlyIncreasing subsequence =
  (k : Nat) →
  subsequence k <ₙ subsequence (suc k)

Compact :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Region R n →
  Set
Compact {R} {n} reals body =
  (sequence : Nat → Vector R n) →
  ((k : Nat) → body (sequence k)) →
  Exists (Nat → Nat)
    (λ subsequence →
      StrictlyIncreasing subsequence ∧
      Exists (Vector R n)
        (λ limit →
          VectorConvergesTo reals
            (λ k → sequence (subsequence k))
            limit ∧
          body limit))

Empty :
  {R : Set} →
  {n : Nat} →
  Region R n
Empty _ =
  ⊥

Complement :
  {R : Set} →
  {n : Nat} →
  Region R n →
  Region R n
Complement body x =
  body x → ⊥

UnionAll :
  {R : Set} →
  {n : Nat} →
  (Nat → Region R n) →
  Region R n
UnionAll regions x =
  Exists Nat (λ k → regions k x)

Disjoint :
  {R : Set} →
  {n : Nat} →
  Region R n →
  Region R n →
  Set
Disjoint {R} {n} leftBody rightBody =
  (x : Vector R n) →
  leftBody x →
  rightBody x →
  ⊥

PairwiseDisjoint :
  {R : Set} →
  {n : Nat} →
  (Nat → Region R n) →
  Set
PairwiseDisjoint regions =
  (m n : Nat) →
  m ≠ n →
  Disjoint (regions m) (regions n)

translateRegion :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Vector R n →
  Region R n →
  Region R n
translateRegion {R} {n} reals offset body x =
  Exists (Vector R n)
    (λ y →
      body y ∧
      x ≡ addVector reals offset y)

HalfOpenBox :
  {R : Set} →
  {n : Nat} →
  CompleteOrderedField R →
  Vector R n →
  Vector R n →
  Region R n
HalfOpenBox {R} {n} reals lower upper x =
  (i : Fin n) →
  LessOrEqual reals (lower i) (x i) ∧
  lessThan reals (x i) (upper i)

productFin :
  {R : Set} →
  CompleteOrderedField R →
  {n : Nat} →
  (Fin n → R) →
  R
productFin reals {zero} values =
  oneR reals
productFin reals {suc n} values =
  multiply reals
    (values fzero)
    (productFin reals (λ i → values (fsuc i)))

data ExtendedNonnegative (R : Set) : Set where
  finite   : R → ExtendedNonnegative R
  infinity : ExtendedNonnegative R

data ExtendedLessOrEqual
  {R : Set}
  (reals : CompleteOrderedField R) :
  ExtendedNonnegative R →
  ExtendedNonnegative R →
  Set where

  finite≤finite :
    {x y : R} →
    LessOrEqual reals x y →
    ExtendedLessOrEqual reals (finite x) (finite y)

  finite≤infinity :
    {x : R} →
    ExtendedLessOrEqual reals (finite x) infinity

  infinity≤infinity :
    ExtendedLessOrEqual reals infinity infinity

data ExtendedLess
  {R : Set}
  (reals : CompleteOrderedField R) :
  ExtendedNonnegative R →
  ExtendedNonnegative R →
  Set where

  finite<finite :
    {x y : R} →
    lessThan reals x y →
    ExtendedLess reals (finite x) (finite y)

  finite<infinity :
    {x : R} →
    ExtendedLess reals (finite x) infinity

addExtended :
  {R : Set} →
  CompleteOrderedField R →
  ExtendedNonnegative R →
  ExtendedNonnegative R →
  ExtendedNonnegative R
addExtended reals infinity rightValue =
  infinity
addExtended reals (finite x) infinity =
  infinity
addExtended reals (finite x) (finite y) =
  finite (add reals x y)

sumFirstExtended :
  {R : Set} →
  CompleteOrderedField R →
  Nat →
  (Nat → ExtendedNonnegative R) →
  ExtendedNonnegative R
sumFirstExtended reals zero term =
  finite (zeroR reals)
sumFirstExtended reals (suc n) term =
  addExtended reals
    (sumFirstExtended reals n term)
    (term n)

UpperBoundExtended :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → ExtendedNonnegative R) →
  ExtendedNonnegative R →
  Set
UpperBoundExtended reals values bound =
  (n : Nat) →
  ExtendedLessOrEqual reals (values n) bound

LeastUpperBoundExtended :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → ExtendedNonnegative R) →
  ExtendedNonnegative R →
  Set
LeastUpperBoundExtended reals values supremum =
  UpperBoundExtended reals values supremum ∧
  ((upper : ExtendedNonnegative _) →
    UpperBoundExtended reals values upper →
    ExtendedLessOrEqual reals supremum upper)

record StandardEuclideanLebesgueMeasure
  {R : Set}
  (reals : CompleteOrderedField R)
  (n : Nat) :
  Set₁ where

  field
    measurable : Region R n → Set
    volume : Region R n → ExtendedNonnegative R

    measurable-empty :
      measurable Empty
    measurable-complement :
      (body : Region R n) →
      measurable body →
      measurable (Complement body)
    measurable-union-all :
      (regions : Nat → Region R n) →
      ((k : Nat) → measurable (regions k)) →
      measurable (UnionAll regions)
    compact-measurable :
      (body : Region R n) →
      Compact reals body →
      measurable body
    measurable-translation :
      (offset : Vector R n) →
      (body : Region R n) →
      measurable body →
      measurable (translateRegion reals offset body)
    measurable-box :
      (lower upper : Vector R n) →
      measurable (HalfOpenBox reals lower upper)

    volume-congruent :
      (leftBody rightBody : Region R n) →
      ((x : Vector R n) →
        leftBody x ↔ rightBody x) →
      volume leftBody ≡ volume rightBody
    volume-empty :
      volume Empty ≡ finite (zeroR reals)
    volume-nonnegative :
      (body : Region R n) →
      measurable body →
      ExtendedLessOrEqual reals
        (finite (zeroR reals))
        (volume body)
    volume-countable-additive :
      (regions : Nat → Region R n) →
      ((k : Nat) → measurable (regions k)) →
      PairwiseDisjoint regions →
      LeastUpperBoundExtended reals
        (λ count →
          sumFirstExtended reals count
            (λ k → volume (regions k)))
        (volume (UnionAll regions))
    volume-translation-invariant :
      (offset : Vector R n) →
      (body : Region R n) →
      measurable body →
      volume (translateRegion reals offset body) ≡
      volume body
    volume-box :
      (lower upper : Vector R n) →
      ((i : Fin n) →
        LessOrEqual reals (lower i) (upper i)) →
      volume (HalfOpenBox reals lower upper) ≡
      finite
        (productFin reals
          (λ i →
            subtract reals (upper i) (lower i)))

module MinkowskiStatement
  {R : Set}
  (n : Nat)
  (reals : CompleteOrderedField R)
  (euclidean : StandardEuclideanLebesgueMeasure reals n)
  where

  open StandardEuclideanLebesgueMeasure euclidean

  blichfeldt-principle : Set₁
  blichfeldt-principle =
    (body : Region R n) →
    measurable body →
    ExtendedLess reals
      (finite (oneR reals))
      (volume body) →
    Exists (Vector R n)
      (λ x →
        Exists (Vector R n)
          (λ y →
            DistinctVectors x y ∧
            (body x ∧
            (body y ∧
             IntegerVector reals
               (subtractVector reals x y)))))

  strict-minkowski : Set₁
  strict-minkowski =
    (body : Region R n) →
    Convex reals body →
    OriginSymmetric reals body →
    measurable body →
    ExtendedLess reals
      (finite (twoPower reals n))
      (volume body) →
    Exists (Vector R n)
      (λ latticePoint →
        NonzeroVector reals latticePoint ∧
        (IntegerVector reals latticePoint ∧
         body latticePoint))

  compact-minkowski : Set₁
  compact-minkowski =
    (body : Region R n) →
    Convex reals body →
    Compact reals body →
    OriginSymmetric reals body →
    ExtendedLessOrEqual reals
      (finite (twoPower reals n))
      (volume body) →
    Exists (Vector R n)
      (λ latticePoint →
        NonzeroVector reals latticePoint ∧
        (IntegerVector reals latticePoint ∧
         body latticePoint))

  record MinkowskiClaims : Set₁ where
    field
      blichfeldt :
        blichfeldt-principle
      strict-form :
        strict-minkowski
      compact-form :
        compact-minkowski

minkowskis-fundamental-theorem : Set₁
minkowskis-fundamental-theorem =
  (R : Set) →
  (n : Nat) →
  PositiveDimension n →
  (reals : CompleteOrderedField R) →
  (euclidean : StandardEuclideanLebesgueMeasure reals n) →
  MinkowskiStatement.MinkowskiClaims n reals euclidean
