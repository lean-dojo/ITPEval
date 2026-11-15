-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/binomial_Top_computeqtvc: the binomial-coefficient computation
-- verification condition for its loop invariant and final result.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module binomial_Top_computeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

boolOr : Bool → Bool → Bool
boolOr true _ = true
boolOr false value = value

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

absoluteInt : Int → Int
absoluteInt (pos n) = pos n
absoluteInt (negsuc n) = pos (suc n)

minimumInt : Int → Int → Int
minimumInt x y with intLessOrEqual x y
... | true = x
... | false = y

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

EuclideanQuotient : Int → Int → Int → Set
EuclideanQuotient dividend divisor quotient =
  Exists Int λ remainder →
    dividend ≡
      addInt (multiplyInt divisor quotient) remainder ∧
    zeroZ ≤Z remainder ∧
    remainder <Z absoluteInt divisor

record BinomialStructure : Set where
  field
    infix-sl : Int → Int → Int
    comb     : Int → Int → Int

    infix-sl-def :
      (y x : Int) →
      y ≠ zeroZ →
      EuclideanQuotient x y (infix-sl x y)

    comb-def :
      (k n : Int) →
      zeroZ ≤Z k →
      k ≤Z n →
      IfSet
        (boolOr (intEqual k zeroZ) (intEqual k n))
        (comb n k ≡ oneZ)
        (comb n k ≡
          addInt
            (comb (subtractInt n oneZ) k)
            (comb (subtractInt n oneZ) (subtractInt k oneZ)))

    comb-spec :
      (k n : Int) →
      zeroZ ≤Z k →
      k ≤Z n →
      oneZ ≤Z comb n k

open BinomialStructure

ComputeVC : BinomialStructure → Int → Int → Set
ComputeVC signature k n =
  zeroZ ≤Z k →
  k ≤Z n →
  let k1 = minimumInt k (subtractInt n k)
  in
  ((oneZ ≤Z addInt k1 oneZ) →
    (((oneZ ≤Z oneZ) ∧
      (oneZ ≤Z addInt k1 oneZ)) ∧
     (oneZ ≡ comb signature n (subtractInt oneZ oneZ))) ∧
    ((r : Int) →
      (((i : Int) →
        (((oneZ ≤Z i) ∧ (i ≤Z k1)) ∧
         ((oneZ ≤Z i) ∧ (i ≤Z addInt k1 oneZ)) ∧
         (r ≡ comb signature n (subtractInt i oneZ))) →
        (i ≠ zeroZ) ∧
        ((oneZ ≤Z addInt i oneZ) ∧
         (addInt i oneZ ≤Z addInt k1 oneZ)) ∧
        (infix-sl
          signature
          (multiplyInt r (addInt (subtractInt n i) oneZ))
          i
          ≡
          comb
            signature
            n
            (subtractInt (addInt i oneZ) oneZ))) ∧
       ((((oneZ ≤Z addInt k1 oneZ) ∧
          (addInt k1 oneZ ≤Z addInt k1 oneZ)) ∧
         (r ≡
          comb
            signature
            n
            (subtractInt (addInt k1 oneZ) oneZ))) →
        r ≡ comb signature n k)))) ∧
  ((addInt k1 oneZ <Z oneZ) →
    oneZ ≡ comb signature n k)

compute'vc : (signature : BinomialStructure) → Set
compute'vc signature =
  (k n : Int) →
  ComputeVC signature k n
