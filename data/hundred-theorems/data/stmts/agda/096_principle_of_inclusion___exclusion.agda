-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__096,
-- "Principle of Inclusion / Exclusion": for a finite enumeration and a list-indexed family
-- of decidable subsets, the cardinality of their union is the alternating sum of the
-- cardinalities of all nonempty subfamily intersections. This file contains no proof.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; lsuc)

infixr 5 _++_
infixl 6 _+z_
infixl 7 _*z_

SetPredicate :
  {a : Level} →
  Set a →
  Set a
SetPredicate X = X → Bool

_++_ :
  {a : Level} →
  {A : Set a} →
  List A →
  List A →
  List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

mapList :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  List A →
  List B
mapList function [] = []
mapList function (x ∷ xs) =
  function x ∷ mapList function xs

filterList :
  {a : Level} →
  {A : Set a} →
  (A → Bool) →
  List A →
  List A
filterList predicate [] = []
filterList predicate (x ∷ xs) with predicate x
... | true = x ∷ filterList predicate xs
... | false = filterList predicate xs

length :
  {a : Level} →
  {A : Set a} →
  List A →
  Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

boolOr : Bool → Bool → Bool
boolOr false right = right
boolOr true right = true

boolAnd : Bool → Bool → Bool
boolAnd false right = false
boolAnd true right = right

emptySet :
  {a : Level} →
  {X : Set a} →
  SetPredicate X
emptySet x = false

binaryUnion :
  {a : Level} →
  {X : Set a} →
  SetPredicate X →
  SetPredicate X →
  SetPredicate X
binaryUnion left right x =
  boolOr (left x) (right x)

binaryIntersection :
  {a : Level} →
  {X : Set a} →
  SetPredicate X →
  SetPredicate X →
  SetPredicate X
binaryIntersection left right x =
  boolAnd (left x) (right x)

foldRight :
  {a : Level} →
  {A : Set a} →
  (A → A → A) →
  A →
  List A →
  A
foldRight operation base [] = base
foldRight operation base (x ∷ xs) =
  operation x (foldRight operation base xs)

foldOne :
  {a : Level} →
  {A : Set a} →
  (A → A → A) →
  List A →
  A →
  A
foldOne operation [] default = default
foldOne operation (x ∷ xs) default =
  foldRight operation x xs

listUnion :
  {a : Level} →
  {X : Set a} →
  List (SetPredicate X) →
  SetPredicate X
listUnion sets =
  foldRight binaryUnion emptySet sets

listIntersection :
  {a : Level} →
  {X : Set a} →
  List (SetPredicate X) →
  SetPredicate X
listIntersection sets =
  foldOne binaryIntersection sets emptySet

sublists :
  {a : Level} →
  {A : Set a} →
  List A →
  List (List A)
sublists [] = [] ∷ []
sublists (x ∷ xs) =
  let xss = sublists xs
  in xss ++ mapList (λ ys → x ∷ ys) xss

nonempty :
  {a : Level} →
  {A : Set a} →
  List A →
  Bool
nonempty [] = false
nonempty (x ∷ xs) = true

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

alternatingSign : Nat → Int
alternatingSign zero = pos (suc zero)
alternatingSign (suc n) =
  negateInt (alternatingSign n)

sumInt : List Int → Int
sumInt [] = pos zero
sumInt (x ∷ xs) = x +z sumInt xs

cardinal :
  {a : Level} →
  {X : Set a} →
  List X →
  SetPredicate X →
  Int
cardinal enumeration subset =
  pos (length (filterList subset enumeration))

inclusionExclusionTerm :
  {a : Level} →
  {X : Set a} →
  List X →
  List (SetPredicate X) →
  Int
inclusionExclusionTerm enumeration selected =
  cardinal enumeration (listIntersection selected) *z
  alternatingSign (suc (length selected))

principle-of-inclusion-exclusion :
  {a : Level} →
  Set (lsuc a)
principle-of-inclusion-exclusion {a} =
  (X : Set a) →
  (enumeration : List X) →
  (family : List (SetPredicate X)) →
  cardinal enumeration (listUnion family) ≡
  sumInt
    (mapList
      (inclusionExclusionTerm enumeration)
      (filterList nonempty (sublists family)))
