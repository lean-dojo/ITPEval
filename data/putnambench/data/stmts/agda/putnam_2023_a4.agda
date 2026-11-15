-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_a4
-- (putnambench__agda__putnam_2023_a4): density in real three-space of the
-- integer span of the normalized vertex vectors of a regular icosahedron.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2023A4 where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : {l : Level} -> Set l -> Set l
Not A =
  A -> Bottom

_!=_ : {l : Level} {A : Set l} -> A -> A -> Set l
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists
  {l1 l2 : Level}
  (A : Set l1)
  (P : A -> Set l2) :
  Set (l1 ⊔ l2) where
  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessThan : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR
    negate-involutive :
      (x : R) -> negate (negate x) == x

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-irreflexive :
      (x : R) ->
      lessThan x x ->
      Bottom
    order-transitive :
      (x y z : R) ->
      lessThan x y ->
      lessThan y z ->
      lessThan x z
    order-trichotomy :
      (x y : R) ->
      lessThan x y or
      (x == y or lessThan y x)
    add-order :
      (x y z : R) ->
      lessThan x y ->
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : R) ->
      lessThan zeroR x ->
      lessThan zeroR y ->
      lessThan zeroR (multiply x y)
    zero-less-than-one :
      lessThan zeroR oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) ==
      add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) ==
      multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n -> lessThan x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessThan x upper or x == upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessThan x supremum or x == supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessThan x upper or x == upper) ->
            lessThan supremum upper or supremum == upper))

    square-root-nonnegative :
      (x : R) ->
      lessThan zeroR (squareRoot x) or
      squareRoot x == zeroR
    square-root-square :
      (x : R) ->
      (lessThan zeroR x or x == zeroR) ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      (lessThan x zeroR or x == zeroR) ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      (lessThan zeroR y or y == zeroR) ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

fiveN : Nat
fiveN =
  suc fourN

sixN : Nat
sixN =
  suc fiveN

sevenN : Nat
sevenN =
  suc sixN

eightN : Nat
eightN =
  suc sevenN

nineN : Nat
nineN =
  suc eightN

tenN : Nat
tenN =
  suc nineN

elevenN : Nat
elevenN =
  suc tenN

twelveN : Nat
twelveN =
  suc elevenN

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

Vector3 : Set -> Set
Vector3 R =
  Fin threeN -> R

vec3 :
  {R : Set} ->
  R ->
  R ->
  R ->
  Vector3 R
vec3 x y z fzero =
  x
vec3 x y z (fsuc fzero) =
  y
vec3 x y z (fsuc (fsuc fzero)) =
  z

SameVector :
  {R : Set} ->
  Vector3 R ->
  Vector3 R ->
  Set
SameVector leftVector rightVector =
  (coordinate : Fin threeN) ->
  leftVector coordinate == rightVector coordinate

zeroVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R
zeroVector reals _ =
  zeroR reals

addVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  Vector3 R ->
  Vector3 R
addVector reals x y coordinate =
  add reals (x coordinate) (y coordinate)

negateVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  Vector3 R
negateVector reals x coordinate =
  negate reals (x coordinate)

subtractVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  Vector3 R ->
  Vector3 R
subtractVector reals x y =
  addVector reals x (negateVector reals y)

scaleVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Vector3 R ->
  Vector3 R
scaleVector reals scalar x coordinate =
  multiply reals scalar (x coordinate)

squaredNorm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  R
squaredNorm reals x =
  add reals
    (square reals (x fzero))
    (add reals
      (square reals (x (fsuc fzero)))
      (square reals (x (fsuc (fsuc fzero)))))

norm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  R
norm reals x =
  squareRoot reals (squaredNorm reals x)

record LinearIsometryEquivalence
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where
  field
    toFunction inverseFunction :
      Vector3 R -> Vector3 R

    to-additive :
      (x y : Vector3 R) ->
      SameVector
        (toFunction (addVector reals x y))
        (addVector reals (toFunction x) (toFunction y))
    to-scaled :
      (scalar : R) ->
      (x : Vector3 R) ->
      SameVector
        (toFunction (scaleVector reals scalar x))
        (scaleVector reals scalar (toFunction x))

    left-inverse :
      (x : Vector3 R) ->
      SameVector
        (inverseFunction (toFunction x))
        x
    right-inverse :
      (x : Vector3 R) ->
      SameVector
        (toFunction (inverseFunction x))
        x

    norm-preserving :
      (x : Vector3 R) ->
      norm reals (toFunction x) == norm reals x

open LinearIsometryEquivalence

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} terms =
  zeroR reals
sumFin reals {suc n} terms =
  add reals
    (terms fzero)
    (sumFin reals (\ i -> terms (fsuc i)))

module Putnam2023A4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  phi : R
  phi =
    divide reals
      (add reals
        (oneR reals)
        (squareRoot reals (fromNat reals fiveN)))
      (fromNat reals twoN)

  normalization : R
  normalization =
    squareRoot reals
      (add reals
        (oneR reals)
        (square reals phi))

  canonicalVector :
    Fin twelveN ->
    Vector3 R
  canonicalVector fzero =
    vec3 (oneR reals) phi (zeroR reals)
  canonicalVector (fsuc fzero) =
    vec3 (negate reals (oneR reals)) phi (zeroR reals)
  canonicalVector (fsuc (fsuc fzero)) =
    vec3 (oneR reals) (negate reals phi) (zeroR reals)
  canonicalVector (fsuc (fsuc (fsuc fzero))) =
    vec3 (negate reals (oneR reals)) (negate reals phi) (zeroR reals)
  canonicalVector (fsuc (fsuc (fsuc (fsuc fzero)))) =
    vec3 phi (zeroR reals) (oneR reals)
  canonicalVector (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) =
    vec3 phi (zeroR reals) (negate reals (oneR reals))
  canonicalVector (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) =
    vec3 (negate reals phi) (zeroR reals) (oneR reals)
  canonicalVector (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) =
    vec3 (negate reals phi) (zeroR reals) (negate reals (oneR reals))
  canonicalVector
    (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) =
    vec3 (zeroR reals) (oneR reals) phi
  canonicalVector
    (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) =
    vec3 (zeroR reals) (negate reals (oneR reals)) phi
  canonicalVector
    (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) =
    vec3 (zeroR reals) (oneR reals) (negate reals phi)
  canonicalVector
    (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) =
    vec3
      (zeroR reals)
      (negate reals (oneR reals))
      (negate reals phi)

  normalizedCanonicalVector :
    Fin twelveN ->
    Vector3 R
  normalizedCanonicalVector i =
    scaleVector reals
      (inverse reals normalization)
      (canonicalVector i)

  IcosahedronModel :
    (Fin twelveN -> Vector3 R) ->
    Set1
  IcosahedronModel v =
    Exists (LinearIsometryEquivalence reals)
      (\ isometry ->
        (i : Fin twelveN) ->
        SameVector
          (toFunction isometry (v i))
          (normalizedCanonicalVector i))

  integerCombination :
    (Fin twelveN -> Vector3 R) ->
    (Fin twelveN -> Int) ->
    Vector3 R
  integerCombination v coefficients coordinate =
    sumFin reals
      (\ i ->
        multiply reals
          (fromInt reals (coefficients i))
          (v i coordinate))

  proposition : Set1
  proposition =
    (v : Fin twelveN -> Vector3 R) ->
    IcosahedronModel v ->
    (w : Vector3 R) ->
    (epsilon : R) ->
    lessThan reals (zeroR reals) epsilon ->
    Exists (Fin twelveN -> Int)
      (\ coefficients ->
        lessThan reals
          (norm reals
            (subtractVector reals
              (integerCombination v coefficients)
              w))
          epsilon)

putnam-2023-a4 : Set1
putnam-2023-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2023A4Statement.proposition reals
