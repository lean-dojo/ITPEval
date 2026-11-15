-- Statement-only formalization of thousand-theorems corpus artifact Q2226677,
-- "Gelfand–Mazur theorem": the canonical scalar map from the complex numbers
-- to a complete complex normed ring whose nonzero elements are exactly its
-- units is an algebra equivalence. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2226677_gelfand_mazur_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _!=_ _<N_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero<successor : {n : Nat} -> zero <N suc n
  successor<successor :
    {m n : Nat} ->
    m <N n ->
    suc m <N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) ->
      addR x zeroR == x
    add-inverseR :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) ->
      lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) :
  Set1 where

  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) ->
      forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) ->
      backwardR (forwardR x) == x
    forward-zeroR :
      forwardR (zeroR source) == zeroR target
    forward-oneR :
      forwardR (oneR source) == oneR target
    forward-addR :
      (x y : R) ->
      forwardR (addR source x y) ==
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) ->
      forwardR (multiplyR source x y) ==
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) ->
      forwardR (negateR source x) ==
      negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) ->
      forwardR (reciprocalR source x) ==
      reciprocalR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) == fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set2 where

  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

zeroC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
zeroC reals =
  complex (zeroR reals) (zeroR reals)

oneC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R
oneC reals =
  complex (oneR reals) (zeroR reals)

addC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
addC reals (complex a b) (complex c d) =
  complex
    (addR reals a c)
    (addR reals b d)

negateC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R
negateC reals (complex a b) =
  complex
    (negateR reals a)
    (negateR reals b)

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

multiplyC :
  {R : Set} ->
  CompleteOrderedField R ->
  Complex R ->
  Complex R ->
  Complex R
multiplyC reals (complex a b) (complex c d) =
  complex
    (subtractR reals
      (multiplyR reals a c)
      (multiplyR reals b d))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

record ComplexNorm
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    normC : Complex R -> R
    norm-nonnegativeC :
      (z : Complex R) ->
      lessOrEqualR reals (zeroR reals) (normC z)
    norm-zeroC :
      normC (zeroC reals) == zeroR reals
    norm-zero-onlyC :
      (z : Complex R) ->
      normC z == zeroR reals ->
      z == zeroC reals
    norm-negateC :
      (z : Complex R) ->
      normC (negateC reals z) == normC z
    norm-addC :
      (z w : Complex R) ->
      lessOrEqualR reals
        (normC (addC reals z w))
        (addR reals (normC z) (normC w))
    norm-multiplyC :
      (z w : Complex R) ->
      normC (multiplyC reals z w) ==
      multiplyR reals (normC z) (normC w)
    norm-squareC :
      (z : Complex R) ->
      multiplyR reals (normC z) (normC z) ==
      addR reals
        (multiplyR reals (realPart z) (realPart z))
        (multiplyR reals (imaginaryPart z) (imaginaryPart z))

open ComplexNorm

record NormedRing
  {a : Level}
  {R : Set}
  (reals : CompleteOrderedField R)
  (A : Set a) :
  Set (lsuc a) where

  field
    zeroA oneA : A
    addA multiplyA : A -> A -> A
    negateA : A -> A
    normA : A -> R

    add-commutativeA :
      (x y : A) ->
      addA x y == addA y x
    add-associativeA :
      (x y z : A) ->
      addA (addA x y) z == addA x (addA y z)
    add-zeroA :
      (x : A) ->
      addA x zeroA == x
    add-inverseA :
      (x : A) ->
      addA x (negateA x) == zeroA

    multiply-associativeA :
      (x y z : A) ->
      multiplyA (multiplyA x y) z ==
      multiplyA x (multiplyA y z)
    multiply-one-leftA :
      (x : A) ->
      multiplyA oneA x == x
    multiply-one-rightA :
      (x : A) ->
      multiplyA x oneA == x
    distribute-leftA :
      (x y z : A) ->
      multiplyA x (addA y z) ==
      addA (multiplyA x y) (multiplyA x z)
    distribute-rightA :
      (x y z : A) ->
      multiplyA (addA x y) z ==
      addA (multiplyA x z) (multiplyA y z)

    norm-nonnegativeA :
      (x : A) ->
      lessOrEqualR reals (zeroR reals) (normA x)
    norm-zeroA :
      normA zeroA == zeroR reals
    norm-zero-onlyA :
      (x : A) ->
      normA x == zeroR reals ->
      x == zeroA
    norm-negateA :
      (x : A) ->
      normA (negateA x) == normA x
    norm-addA :
      (x y : A) ->
      lessOrEqualR reals
        (normA (addA x y))
        (addR reals (normA x) (normA y))
    norm-multiplyA :
      (x y : A) ->
      lessOrEqualR reals
        (normA (multiplyA x y))
        (multiplyR reals (normA x) (normA y))

open NormedRing

subtractA :
  {a : Level} ->
  {R : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  NormedRing reals A ->
  A ->
  A ->
  A
subtractA ring x y =
  addA ring x (negateA ring y)

distanceA :
  {a : Level} ->
  {R : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  NormedRing reals A ->
  A ->
  A ->
  R
distanceA ring x y =
  normA ring (subtractA ring x y)

SequentialLimit :
  {a : Level} ->
  {R : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  NormedRing reals A ->
  (Nat -> A) ->
  A ->
  Set
SequentialLimit {R = R} {reals = reals} ring sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <N suc n ->
      StrictLess reals (distanceA ring (sequence n) limit) epsilon)

CauchySequence :
  {a : Level} ->
  {R : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  NormedRing reals A ->
  (Nat -> A) ->
  Set
CauchySequence {R = R} {reals = reals} ring sequence =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <N suc m ->
      cutoff <N suc n ->
      StrictLess reals
        (distanceA ring (sequence m) (sequence n))
        epsilon)

Complete :
  {a : Level} ->
  {R : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  NormedRing reals A ->
  Set a
Complete {A = A} ring =
  (sequence : Nat -> A) ->
  CauchySequence ring sequence ->
  Exists A (\ limit -> SequentialLimit ring sequence limit)

record NormedComplexAlgebra
  {a : Level}
  {R : Set}
  {A : Set a}
  (reals : CompleteOrderedField R)
  (complexNorm : ComplexNorm reals)
  (ring : NormedRing reals A) :
  Set (lsuc a) where

  field
    scalarMap : Complex R -> A
    map-zero :
      scalarMap (zeroC reals) == zeroA ring
    map-one :
      scalarMap (oneC reals) == oneA ring
    map-add :
      (z w : Complex R) ->
      scalarMap (addC reals z w) ==
      addA ring (scalarMap z) (scalarMap w)
    map-multiply :
      (z w : Complex R) ->
      scalarMap (multiplyC reals z w) ==
      multiplyA ring (scalarMap z) (scalarMap w)
    scalar-central :
      (z : Complex R) ->
      (x : A) ->
      multiplyA ring (scalarMap z) x ==
      multiplyA ring x (scalarMap z)
    norm-scalar-multiply :
      (z : Complex R) ->
      (x : A) ->
      lessOrEqualR reals
        (normA ring (multiplyA ring (scalarMap z) x))
        (multiplyR reals (normC complexNorm z) (normA ring x))

open NormedComplexAlgebra

IsUnit :
  {a : Level} ->
  {R : Set} ->
  {A : Set a} ->
  {reals : CompleteOrderedField R} ->
  NormedRing reals A ->
  A ->
  Set a
IsUnit {A = A} ring x =
  Σ A
    (\ inverse ->
      Both
        (multiplyA ring x inverse == oneA ring)
        (multiplyA ring inverse x == oneA ring))

record AlgebraEquivalenceViaScalarMap
  {a : Level}
  {R : Set}
  {A : Set a}
  {reals : CompleteOrderedField R}
  {complexNorm : ComplexNorm reals}
  {ring : NormedRing reals A}
  (algebra : NormedComplexAlgebra reals complexNorm ring) :
  Set (lsuc a) where

  field
    inverse : A -> Complex R
    inverse-after-scalar-map :
      (z : Complex R) ->
      inverse (scalarMap algebra z) == z
    scalar-map-after-inverse :
      (x : A) ->
      scalarMap algebra (inverse x) == x

gelfand-mazur-theorem :
  (a : Level) ->
  Set (lsuc (lsuc lzero) ⊔ lsuc a)
gelfand-mazur-theorem a =
  (R : Set) ->
  (A : Set a) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (complexNorm : ComplexNorm reals) ->
  (ring : NormedRing reals A) ->
  (algebra : NormedComplexAlgebra reals complexNorm ring) ->
  Complete ring ->
  ((a : A) -> Iff (IsUnit ring a) (a != zeroA ring)) ->
  AlgebraEquivalenceViaScalarMap algebra
