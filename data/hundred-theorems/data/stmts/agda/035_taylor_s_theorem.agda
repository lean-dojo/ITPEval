-- Statement-only formalization of corpus artifact hundred-theorems__agda__035,
-- "Taylor's Theorem": a real function with a continuous derivative hierarchy is
-- its Taylor polynomial plus a Lagrange remainder at an intermediate point.
-- This file contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero <N suc n
  succ<succ : {m n : Nat} -> m <N n -> suc m <N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqual x y) (lessOrEqual y x)
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      Both (lessOrEqual zeroR oneR) (zeroR != oneR)

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  Both
    (StrictLess reals (subtract reals center radius) x)
    (StrictLess reals x (add reals center radius))

ContinuousWithin :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  Set
ContinuousWithin {R} reals f domain point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          domain y ->
          CloseTo reals point delta y ->
          CloseTo reals (f point) epsilon (f y)))

differenceQuotient :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals f x y =
  divide reals
    (subtract reals (f y) (f x))
    (subtract reals y x)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals f x derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          CloseTo reals x delta y ->
          y != x ->
          CloseTo reals derivative epsilon
            (differenceQuotient reals f x y)))

InClosedInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
InClosedInterval reals a b x =
  Either
    (Both
      (lessOrEqual reals a x)
      (lessOrEqual reals x b))
    (Both
      (lessOrEqual reals b x)
      (lessOrEqual reals x a))

StrictlyBetween :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
StrictlyBetween reals a b x =
  Either
    (Both
      (StrictLess reals a x)
      (StrictLess reals x b))
    (Both
      (StrictLess reals b x)
      (StrictLess reals x a))

power :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
power reals x zero =
  oneR reals
power reals x (suc n) =
  multiply reals (power reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals term zero =
  zeroR reals
sumFirst reals term (suc n) =
  add reals
    (sumFirst reals term n)
    (term n)

taylorTerm :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Nat -> R -> R) ->
  R ->
  R ->
  Nat ->
  R
taylorTerm reals derivatives center x n =
  multiply reals
    (divide reals
      (derivatives n center)
      (fromNat reals (factorial n)))
    (power reals (subtract reals x center) n)

taylorPolynomial :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Nat -> R -> R) ->
  R ->
  R ->
  Nat ->
  R
taylorPolynomial reals derivatives center x n =
  sumFirst reals
    (taylorTerm reals derivatives center x)
    n

taylorRemainder :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Nat -> R -> R) ->
  R ->
  R ->
  Nat ->
  R ->
  R
taylorRemainder reals derivatives center x n intermediate =
  multiply reals
    (divide reals
      (derivatives n intermediate)
      (fromNat reals (factorial n)))
    (power reals (subtract reals x center) n)

taylor-theorem : Set1
taylor-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (f : R -> R) ->
  (derivatives : Nat -> R -> R) ->
  (center x : R) ->
  (n : Nat) ->
  zero <N n ->
  center != x ->
  ((point : R) ->
    derivatives zero point == f point) ->
  ((m : Nat) ->
    m <N n ->
    (point : R) ->
    InClosedInterval reals center x point ->
    ContinuousWithin reals
      (derivatives m)
      (InClosedInterval reals center x)
      point) ->
  ((m : Nat) ->
    m <N n ->
    (point : R) ->
    StrictlyBetween reals center x point ->
    DerivativeAt reals
      (derivatives m)
      point
      (derivatives (suc m) point)) ->
  Exists R
    (\ intermediate ->
      Both
        (StrictlyBetween reals center x intermediate)
        (f x ==
          add reals
            (taylorPolynomial reals derivatives center x n)
            (taylorRemainder reals derivatives center x n intermediate)))
