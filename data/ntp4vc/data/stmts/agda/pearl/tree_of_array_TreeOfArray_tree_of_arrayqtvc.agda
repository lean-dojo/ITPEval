-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/tree_of_array_TreeOfArray_tree_of_arrayqtvc: the verification
-- condition for building an inorder-preserving binary tree of logarithmic
-- height from an array. This file contains no proof.

{-# OPTIONS --safe #-}

module tree_of_array_TreeOfArray_tree_of_arrayqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

powerNat : Int → Nat → Int
powerNat base zero = pos (suc zero)
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent = powerNat base (toNat exponent)

maxInt : Int → Int → Int
maxInt x y with intLess x y
... | true = y
... | false = x

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

data Tree (A : Set) : Set where
  Empty : Tree A
  Node  : Tree A → A → Tree A → Tree A

size : {A : Set} → Tree A → Int
size Empty = zeroZ
size (Node left value right) =
  addInt (addInt oneZ (size left)) (size right)

height : {A : Set} → Tree A → Int
height Empty = zeroZ
height (Node left value right) =
  addInt oneZ (maxInt (height left) (height right))

inorder : {A : Set} → Tree A → List A
inorder Empty = []
inorder (Node left value right) =
  append (inorder left) (value ∷ inorder right)

auxiliaryResult :
  {A : Set} → List A → Int → Tree A → Set
auxiliaryResult a o1 result =
  let n = subtractInt o1 zeroZ
  in
  size result ≡ n
  ∧ inorder result ≡
      drop zero
        (take (natSubtract (toNat o1) zero) a)
  ∧
  (zeroZ <Z n →
    let h = height result
    in
    powerInt twoZ (subtractInt h oneZ) ≤Z n
    ∧ n <Z powerInt twoZ h)

finalResult :
  {A : Set} → List A → Tree A → Set
finalResult a result =
  inorder result ≡
    drop zero
      (take (natSubtract (length a) zero) a)
  ∧
  (zeroZ <Z size result →
    let h = height result
    in
    powerInt twoZ (subtractInt h oneZ) ≤Z size result
    ∧ size result <Z powerInt twoZ h)

tree-of-array'vc : Set₁
tree-of-array'vc =
  (A : Set) →
  (a : List A) →
  let o1 = lengthZ a
  in
  ((zeroZ ≤Z zeroZ) ∧
   (zeroZ ≤Z o1) ∧
   (o1 ≤Z lengthZ a))
  ∧
  ((result : Tree A) →
    auxiliaryResult a o1 result →
    finalResult a result)
