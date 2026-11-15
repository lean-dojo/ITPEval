-- Statement-only formalization of "The Prime Number Theorem" from Hundred Theorems item 005.
-- This file contains no proof.

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat
  using (Nat; zero; suc; _+_; _*_; mod-helper)

data Bottom : Set where

NotEqual : {A : Set} -> A -> A -> Set
NotEqual x y = x == y -> Bottom

record Both (A B : Set) : Set where
  constructor pair
  field
    left  : A
    right : B

data Either (A B : Set) : Set where
  first  : A -> Either A B
  second : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

natEqual : Nat -> Nat -> Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

boolNot : Bool -> Bool
boolNot false = true
boolNot true = false

boolOr : Bool -> Bool -> Bool
boolOr false value = value
boolOr true _ = true

dividesBool : Nat -> Nat -> Bool
dividesBool divisor dividend =
  natEqual (naturalMod dividend divisor) zero

hasDivisorThrough : Nat -> Nat -> Bool
hasDivisorThrough n zero = false
hasDivisorThrough n (suc zero) = false
hasDivisorThrough n (suc (suc bound)) =
  boolOr
    (dividesBool (suc (suc bound)) n)
    (hasDivisorThrough n (suc bound))

isPrimeBool : Nat -> Bool
isPrimeBool zero = false
isPrimeBool (suc zero) = false
isPrimeBool (suc (suc n)) =
  boolNot (hasDivisorThrough (suc (suc n)) (suc n))

Prime : Nat -> Set
Prime n = isPrimeBool n == true

indicator : Bool -> Nat
indicator false = zero
indicator true = suc zero

-- This recursion counts exactly the primes in the initial segment [0, n].
primeCount : Nat -> Nat
primeCount zero = zero
primeCount (suc n) =
  primeCount n + indicator (isPrimeBool (suc n))

record StandardRealAnalysis (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate reciprocal : R -> R
    lessOrEqual : R -> R -> Set
    absoluteValue : R -> R
    fromNat : Nat -> R

    one-not-zero :
      NotEqual oneR zeroR

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
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    multiply-inverse :
      (x : R) ->
      NotEqual x zeroR ->
      multiply x (reciprocal x) == oneR

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

    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      absoluteValue x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      absoluteValue x == negate x

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    completeness :
      (S : R -> Set) ->
      Exists R S ->
      Exists R
        (\ bound ->
          (x : R) -> S x -> lessOrEqual x bound) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> S x -> lessOrEqual x supremum)
            ((bound : R) ->
              ((x : R) -> S x -> lessOrEqual x bound) ->
              lessOrEqual supremum bound))

subtract :
  {R : Set} ->
  StandardRealAnalysis R ->
  R ->
  R ->
  R
subtract reals x y =
  StandardRealAnalysis.add reals
    x
    (StandardRealAnalysis.negate reals y)

divide :
  {R : Set} ->
  StandardRealAnalysis R ->
  R ->
  R ->
  R
divide reals x y =
  StandardRealAnalysis.multiply reals
    x
    (StandardRealAnalysis.reciprocal reals y)

StrictLess :
  {R : Set} ->
  StandardRealAnalysis R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both
    (StandardRealAnalysis.lessOrEqual reals x y)
    (NotEqual x y)

SequentialLimit :
  {R : Set} ->
  StandardRealAnalysis R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (StandardRealAnalysis.zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <= n ->
      StandardRealAnalysis.lessOrEqual reals
        (StandardRealAnalysis.absoluteValue reals
          (subtract reals (sequence n) limit))
        epsilon)

power :
  {R : Set} ->
  StandardRealAnalysis R ->
  R ->
  Nat ->
  R
power reals x zero =
  StandardRealAnalysis.oneR reals
power reals x (suc n) =
  StandardRealAnalysis.multiply reals x (power reals x n)

-- For x > 0, this is the standard expansion
-- log x = 2 * sum_j ((x - 1) / (x + 1))^(2j+1) / (2j+1).
naturalLogPartial :
  {R : Set} ->
  StandardRealAnalysis R ->
  R ->
  Nat ->
  R
naturalLogPartial reals x zero =
  StandardRealAnalysis.zeroR reals
naturalLogPartial reals x (suc count) =
  StandardRealAnalysis.add reals
    (naturalLogPartial reals x count)
    (StandardRealAnalysis.multiply reals
      (StandardRealAnalysis.fromNat reals (suc (suc zero)))
      (divide reals
        (power reals
          (divide reals
            (subtract reals x (StandardRealAnalysis.oneR reals))
            (StandardRealAnalysis.add reals
              x
              (StandardRealAnalysis.oneR reals)))
          (suc (count + count)))
        (StandardRealAnalysis.fromNat reals (suc (count + count)))))

NaturalLogValue :
  {R : Set} ->
  StandardRealAnalysis R ->
  R ->
  R ->
  Set
NaturalLogValue reals x value =
  Both
    (StrictLess reals (StandardRealAnalysis.zeroR reals) x)
    (SequentialLimit reals (naturalLogPartial reals x) value)

primeNumberRatio :
  {R : Set} ->
  StandardRealAnalysis R ->
  Nat ->
  R ->
  R
primeNumberRatio reals n logarithm =
  divide reals
    (StandardRealAnalysis.fromNat reals (primeCount n))
    (divide reals
      (StandardRealAnalysis.fromNat reals n)
      logarithm)

the-prime-number-theorem : Set₁
the-prime-number-theorem =
  (R : Set) ->
  (reals : StandardRealAnalysis R) ->
  (epsilon : R) ->
  StrictLess reals (StandardRealAnalysis.zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <= n ->
      Exists R
        (\ logarithm ->
          Both
            (NaturalLogValue reals
              (StandardRealAnalysis.fromNat reals n)
              logarithm)
            (StrictLess reals
              (StandardRealAnalysis.absoluteValue reals
                (subtract reals
                  (primeNumberRatio reals n logarithm)
                  (StandardRealAnalysis.oneR reals)))
              epsilon)))
