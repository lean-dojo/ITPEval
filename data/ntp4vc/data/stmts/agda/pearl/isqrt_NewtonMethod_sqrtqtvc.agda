-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/isqrt_NewtonMethod_sqrtqtvc: the Newton-method integer-square-root
-- verification condition, including truncation-toward-zero division,
-- initialization, loop preservation, and the square-root specification.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module isqrt_NewtonMethod_sqrtqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; div-helper)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

negativeNat : Nat → Int
negativeNat zero = pos zero
negativeNat (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negativeNat n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negativeNat (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negativeNat (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

truncateDivide : Int → Int → Int
truncateDivide (pos n) (pos zero) = pos zero
truncateDivide (pos n) (pos (suc m)) =
  pos (natDivide n (suc m))
truncateDivide (pos n) (negsuc m) =
  negativeNat (natDivide n (suc m))
truncateDivide (negsuc n) (pos zero) = pos zero
truncateDivide (negsuc n) (pos (suc m)) =
  negativeNat (natDivide (suc n) (suc m))
truncateDivide (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

zeroZ oneZ twoZ threeZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))

square : Int → Int
square x = multiplyInt x x

isqrtSpec : Int → Int → Set
isqrtSpec x result =
  zeroZ ≤Z result
  ∧ square result ≤Z x
  ∧ x <Z square (addInt result oneZ)

newtonStep : Int → Int → Int
newtonStep x estimate =
  truncateDivide
    (addInt (truncateDivide x estimate) estimate)
    twoZ

NewtonDecreaseConclusion : Int → Int → Set
NewtonDecreaseConclusion x y =
  let next = newtonStep x y
      next-next = newtonStep x next
  in
  next ≠ zeroZ
  ∧ twoZ ≠ zeroZ
  ∧ (zeroZ ≤Z y ∧ next <Z y)
  ∧ zeroZ <Z next-next
  ∧ zeroZ <Z next
  ∧ x <Z square (addInt next oneZ)
  ∧ x <Z square (addInt next-next oneZ)

NewtonLoopCondition : Int → Set
NewtonLoopCondition x =
  (y : Int) →
  let next = newtonStep x y
  in
  zeroZ <Z next
  ∧ zeroZ <Z y
  ∧ x <Z square (addInt y oneZ)
  ∧ x <Z square (addInt next oneZ) →
  IfSet
    (intLess next y)
    (NewtonDecreaseConclusion x y)
    (isqrtSpec x y)

NewtonInitialization : Int → Set
NewtonInitialization x =
  let first = truncateDivide (addInt oneZ x) twoZ
  in
  zeroZ <Z first
  ∧ zeroZ <Z x
  ∧ first ≡ newtonStep x x
  ∧ x <Z square (addInt x oneZ)
  ∧ x <Z square (addInt first oneZ)

sqrt'vc : Set
sqrt'vc =
  (x : Int) →
  zeroZ ≤Z x →
  IfSet
    (intEqual x zeroZ)
    (isqrtSpec x zeroZ)
    (IfSet
      (intLessOrEqual x threeZ)
      (isqrtSpec x oneZ)
      (twoZ ≠ zeroZ
       ∧ NewtonInitialization x
       ∧ NewtonLoopCondition x))
