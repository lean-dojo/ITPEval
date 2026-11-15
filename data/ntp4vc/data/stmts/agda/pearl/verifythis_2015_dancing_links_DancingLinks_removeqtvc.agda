-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2015_dancing_links_DancingLinks_removeqtvc: the dancing-links
-- removal verification condition, relating two pointer-array updates to removal
-- from a valid circular list. This file contains no proof.

{-# OPTIONS --safe #-}

module DancingLinksRemoveQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

lengthNat : {A : Set} → List A → Nat
lengthNat [] = zero
lengthNat (_ ∷ xs) = suc (lengthNat xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (lengthNat xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

setInt : List Int → Int → Int → List Int
setInt xs index value = setAt xs (toNat index) value

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

updateInt :
  (Int → Int) →
  Int →
  Int →
  Int →
  Int
updateInt old key value query with intEqual query key
... | true = value
... | false = old query

PointwiseEqual :
  (Int → Int) →
  (Int → Int) →
  Set
PointwiseEqual f g =
  (x : Int) → f x ≡ g x

record DLLModel : Set₁ where
  field
    DLL        : Set
    defaultDLL : DLL
    prev       : DLL → List Int
    next       : DLL → List Int
    n          : DLL → Int

open DLLModel

DLLInvariant :
  (model : DLLModel) →
  DLL model →
  Set
DLLInvariant model self =
  lengthNat (prev model self) ≡ lengthNat (next model self)
  ∧ lengthZ (next model self) ≡ n model self

DLLEqual :
  (model : DLLModel) →
  DLL model →
  DLL model →
  Set
DLLEqual model a b =
  prev model a ≡ prev model b
  ∧ next model a ≡ next model b
  ∧ n model a ≡ n model b

record DLLLaws (model : DLLModel) : Set where
  field
    invariant :
      (self : DLL model) →
      DLLInvariant model self

    injective :
      (a b : DLL model) →
      DLLEqual model a b →
      a ≡ b

InRange : List Int → Int → Set
InRange values index =
  zeroZ ≤Z index ∧ index <Z lengthZ values

ArrayPointwiseEqual :
  List Int →
  (Int → Int) →
  (Int → Int) →
  Set
ArrayPointwiseEqual entries f g =
  (index : Int) →
  InRange entries index →
  f index ≡ g index

validIn :
  (model : DLLModel) →
  DLL model →
  Int →
  Set
validIn model l i =
  (zeroZ ≤Z i ∧ i <Z n model l)
  ∧ (zeroZ ≤Z nthInt (prev model l) i
     ∧ nthInt (prev model l) i <Z n model l)
  ∧ (zeroZ ≤Z nthInt (next model l) i
     ∧ nthInt (next model l) i <Z n model l)
  ∧ nthInt (next model l) (nthInt (prev model l) i) ≡ i
  ∧ nthInt (prev model l) (nthInt (next model l) i) ≡ i

validOut :
  (model : DLLModel) →
  DLL model →
  Int →
  Set
validOut model l i =
  (zeroZ ≤Z i ∧ i <Z n model l)
  ∧ (zeroZ ≤Z nthInt (prev model l) i
     ∧ nthInt (prev model l) i <Z n model l)
  ∧ (zeroZ ≤Z nthInt (next model l) i
     ∧ nthInt (next model l) i <Z n model l)
  ∧ nthInt (next model l) (nthInt (prev model l) i)
      ≡ nthInt (next model l) i
  ∧ nthInt (prev model l) (nthInt (next model l) i)
      ≡ nthInt (prev model l) i

isList :
  (model : DLLModel) →
  DLL model →
  List Int →
  Set
isList model l s =
  (k : Int) →
  (zeroZ ≤Z k ∧ k <Z lengthZ s) →
  (zeroZ ≤Z nthInt s k ∧ nthInt s k <Z n model l)
  ∧ nthInt (prev model l) (nthInt s k)
      ≡ nthInt s
          (IfInt
            (intEqual k zeroZ)
            (subtractInt (lengthZ s) oneZ)
            (subtractInt k oneZ))
  ∧ nthInt (next model l) (nthInt s k)
      ≡ nthInt s
          (IfInt
            (intEqual k (subtractInt (lengthZ s) oneZ))
            zeroZ
            (addInt k oneZ))
  ∧ ((k′ : Int) →
      (zeroZ ≤Z k′ ∧ k′ <Z lengthZ s) →
      Not (k ≡ k′) →
      Not (nthInt s k ≡ nthInt s k′))

remove'vc : Set₁
remove'vc =
  (model : DLLModel) →
  (laws : DLLLaws model) →
  (l : DLL model) →
  (i : Int) →
  (s : List Int) →
  validIn model l i →
  isList model l (i ∷ s) →
  let
    o1 = prev model l
  in
  InRange o1 i
  ∧
  (let
     o2 = nthInt o1 i
     o3 = next model l
   in
   InRange o3 i
   ∧
   (let
      o4 = nthInt o3 i
      o5 = prev model l
      updatedPrev = setInt o5 o4 o2
    in
    InRange o5 o4
    ∧
    (lengthNat updatedPrev ≡ lengthNat o5 →
     lengthNat updatedPrev ≡ lengthNat (prev model l) →
     ArrayPointwiseEqual updatedPrev
       (nthInt updatedPrev)
       (updateInt (nthInt o5) o4 o2) →
     InRange (next model l) i
     ∧
     (let
        o6 = nthInt (next model l) i
      in
      InRange updatedPrev i
      ∧
      (let
         o7 = nthInt updatedPrev i
         updatedNext = setInt (next model l) o7 o6
       in
       InRange (next model l) o7
       ∧
       ((l1 : DLL model) →
        lengthNat updatedNext ≡ lengthNat (next model l) →
        lengthNat updatedNext ≡ lengthNat (next model l) →
        ArrayPointwiseEqual updatedNext
          (nthInt updatedNext)
          (updateInt (nthInt (next model l)) o7 o6) →
        (lengthNat updatedPrev ≡ lengthNat updatedNext
         ∧ lengthZ updatedNext ≡ n model l)
        ∧
        ((n model l ≡ n model l1
          ∧ updatedNext ≡ next model l1
          ∧ updatedPrev ≡ prev model l1) →
         validOut model l1 i
         ∧ isList model l1 s)))))))
