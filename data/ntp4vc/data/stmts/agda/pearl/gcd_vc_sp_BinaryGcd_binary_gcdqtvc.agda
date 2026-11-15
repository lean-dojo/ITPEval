-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/gcd_vc_sp_BinaryGcd_binary_gcdqtvc: the binary-GCD verification condition
-- for recursive-call decrease obligations and preservation of the integer
-- greatest common divisor. This file contains no proof.

{-# OPTIONS --safe #-}

module gcd_vc_sp_BinaryGcd_binary_gcdqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

natEven : Nat → Bool
natEven zero = true
natEven (suc zero) = false
natEven (suc (suc n)) = natEven n

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

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

intEven : Int → Bool
intEven (pos n) = natEven n
intEven (negsuc n) = natEven (suc n)

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
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

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

halfInt : Int → Int
halfInt (pos n) = pos (halfNat n)
halfInt (negsuc n) =
  negateInt (pos (halfNat (suc n)))

zeroZ twoZ : Int
zeroZ = pos zero
twoZ = pos (suc (suc zero))

Divides : Int → Int → Set
Divides divisor dividend =
  Exists Int λ quotient →
    dividend ≡ multiplyInt divisor quotient

GreatestCommonDivisor : Int → Int → Int → Set
GreatestCommonDivisor a b g =
  zeroZ ≤Z g
  ∧ Divides g a
  ∧ Divides g b
  ∧ ((d : Int) →
      Divides d a →
      Divides d b →
      Divides d g)

EvenEvenDecrease : Int → Int → Set
EvenEvenDecrease u v =
  let o1 = halfInt v
  in
  twoZ ≠ zeroZ
  ∧
  let o2 = halfInt u
  in
  ((zeroZ ≤Z v ∧ o1 <Z v)
   ∨ (v ≡ o1 ∧ zeroZ ≤Z u ∧ o2 <Z u))
  ∧ zeroZ ≤Z o2
  ∧ zeroZ ≤Z o1

EvenOddDecrease : Int → Int → Set
EvenOddDecrease u v =
  let o1 = halfInt u
  in
  (zeroZ ≤Z u ∧ o1 <Z u)
  ∧ zeroZ ≤Z o1
  ∧ zeroZ ≤Z v

OddEvenDecrease : Int → Int → Set
OddEvenDecrease u v =
  let o1 = halfInt v
  in
  (zeroZ ≤Z v ∧ o1 <Z v)
  ∧ zeroZ ≤Z u
  ∧ zeroZ ≤Z o1

OddOddDecrease : Int → Int → Set
OddOddDecrease u v =
  let o1 = halfInt (subtractInt u v)
  in
  (zeroZ ≤Z u ∧ o1 <Z u)
  ∧ zeroZ ≤Z o1
  ∧ zeroZ ≤Z v

RecursiveDecrease : Int → Int → Set
RecursiveDecrease u v =
  IfSet
    (intLess u v)
    (((zeroZ ≤Z v ∧ u <Z v)
      ∨ (v ≡ u ∧ zeroZ ≤Z u ∧ v <Z u))
     ∧ zeroZ ≤Z v
     ∧ zeroZ ≤Z u)
    (Not (v ≡ zeroZ) →
      twoZ ≠ zeroZ
      ∧ IfSet
          (intEven u)
          (twoZ ≠ zeroZ
           ∧ IfSet
               (intEven v)
               (twoZ ≠ zeroZ ∧ EvenEvenDecrease u v)
               (twoZ ≠ zeroZ ∧ EvenOddDecrease u v))
          (twoZ ≠ zeroZ
           ∧ IfSet
               (intEven v)
               (twoZ ≠ zeroZ ∧ OddEvenDecrease u v)
               (twoZ ≠ zeroZ ∧ OddOddDecrease u v)))

DoubleGcdResult : Int → Int → Int → Set
DoubleGcdResult a b result =
  Exists Int λ g →
    GreatestCommonDivisor a b g
    ∧ result ≡ multiplyInt twoZ g

RecursiveResult : Int → Int → Int → Set
RecursiveResult u v result =
  IfSet
    (intLess u v)
    (GreatestCommonDivisor v u result)
    (IfSet
      (intEqual v zeroZ)
      (result ≡ u)
      (IfSet
        (intEven u)
        (IfSet
          (intEven v)
          (DoubleGcdResult (halfInt u) (halfInt v) result)
          (GreatestCommonDivisor (halfInt u) v result))
        (IfSet
          (intEven v)
          (GreatestCommonDivisor u (halfInt v) result)
          (GreatestCommonDivisor
            (halfInt (subtractInt u v))
            v
            result))))

binary-gcd-vc : Set
binary-gcd-vc =
  (u v : Int) →
  zeroZ ≤Z u →
  zeroZ ≤Z v →
  RecursiveDecrease u v
  ∧
  ((result : Int) →
    RecursiveResult u v result →
    GreatestCommonDivisor u v result)
