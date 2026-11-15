-- Statement-only formalization of "The Fundamental Theorem of Integral Calculus" from Hundred
-- Theorems item 015. This file contains no proof.

module FundamentalTheoremOfIntegralCalculus where

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

DerivativeWithin :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  R ->
  R ->
  Set
DerivativeWithin {R} reals f a b x derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          lessOrEqual reals a y ->
          lessOrEqual reals y b ->
          CloseTo reals x delta y ->
          y != x ->
          CloseTo reals derivative epsilon
            (differenceQuotient reals f x y)))

record TaggedDivision
  {R : Set}
  (reals : CompleteOrderedField R)
  (a b : R) : Set where
  field
    count : Nat
    point : Nat -> R
    tag : Nat -> R

    starts-at :
      point zero == a
    ends-at :
      point count == b
    increasing :
      (i : Nat) ->
      i <N count ->
      StrictLess reals (point i) (point (suc i))
    tag-above-left-endpoint :
      (i : Nat) ->
      i <N count ->
      lessOrEqual reals (point i) (tag i)
    tag-below-right-endpoint :
      (i : Nat) ->
      i <N count ->
      lessOrEqual reals (tag i) (point (suc i))

open TaggedDivision

riemannSumUpTo :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (f : R -> R) ->
  {a b : R} ->
  TaggedDivision reals a b ->
  Nat ->
  R
riemannSumUpTo reals f division zero =
  zeroR reals
riemannSumUpTo reals f division (suc n) =
  add reals
    (riemannSumUpTo reals f division n)
    (multiply reals
      (f (tag division n))
      (subtract reals
        (point division (suc n))
        (point division n)))

riemannSum :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (f : R -> R) ->
  {a b : R} ->
  TaggedDivision reals a b ->
  R
riemannSum reals f division =
  riemannSumUpTo reals f division (count division)

PositiveGaugeOn :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  (R -> R) ->
  Set
PositiveGaugeOn {R} reals a b gauge =
  (x : R) ->
  lessOrEqual reals a x ->
  lessOrEqual reals x b ->
  StrictLess reals (zeroR reals) (gauge x)

Fine :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (gauge : R -> R) ->
  {a b : R} ->
  TaggedDivision reals a b ->
  Set
Fine reals gauge division =
  (i : Nat) ->
  i <N count division ->
  Both
    (StrictLess reals
      (subtract reals
        (tag division i)
        (gauge (tag division i)))
      (point division i))
    (StrictLess reals
      (point division (suc i))
      (add reals
        (tag division i)
        (gauge (tag division i))))

HasGaugeIntegral :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  R ->
  R ->
  Set
HasGaugeIntegral {R} reals f a b integral =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists (R -> R)
    (\ gauge ->
      Both
        (PositiveGaugeOn reals a b gauge)
        ((division : TaggedDivision reals a b) ->
          Fine reals gauge division ->
          CloseTo reals integral epsilon
            (riemannSum reals f division)))

the-fundamental-theorem-of-integral-calculus : Set1
the-fundamental-theorem-of-integral-calculus =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (f derivative : R -> R) ->
  (a b : R) ->
  lessOrEqual reals a b ->
  ((x : R) ->
    lessOrEqual reals a x ->
    lessOrEqual reals x b ->
    DerivativeWithin reals f a b x (derivative x)) ->
  HasGaugeIntegral reals derivative a b
    (subtract reals (f b) (f a))
