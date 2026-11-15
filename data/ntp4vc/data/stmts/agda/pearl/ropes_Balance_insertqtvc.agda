-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/ropes_Balance_insertqtvc: the rope queue insertion verification
-- condition, covering the direct-update and recursive-carry branches while
-- preserving rope invariants and modeled-string concatenation. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module ropes_Balance_insertqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

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

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false = when-true
ifInt false when-true when-false = when-false

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

record StringTheory : Set₁ where
  field
    Char       : Set
    CharString : Set

    dummyChar    : Char
    stringLength : CharString → Int
    stringIndex  : CharString → Int → Char
    emptyString  : CharString
    stringApp    : CharString → CharString → CharString
    stringSub    : CharString → Int → Int → CharString

    lengthNonnegative :
      (s : CharString) →
      zeroZ ≤Z stringLength s

    emptyLength :
      stringLength emptyString ≡ zeroZ

    stringExtensionality :
      (s1 s2 : CharString) →
      ((stringLength s1 ≡ stringLength s2) ∧
       ((i : Int) →
        (zeroZ ≤Z i ∧ i <Z stringLength s1) →
        stringIndex s1 i ≡ stringIndex s2 i)) →
      s1 ≡ s2

    appLength :
      (s1 s2 : CharString) →
      stringLength (stringApp s1 s2) ≡
      addInt (stringLength s1) (stringLength s2)

    appLeft :
      (s1 s2 : CharString) →
      (i : Int) →
      zeroZ ≤Z i →
      i <Z stringLength s1 →
      stringIndex (stringApp s1 s2) i ≡ stringIndex s1 i

    appRight :
      (s1 s2 : CharString) →
      (i : Int) →
      stringLength s1 ≤Z i →
      i <Z addInt (stringLength s1) (stringLength s2) →
      stringIndex (stringApp s1 s2) i ≡
      stringIndex s2 (subtractInt i (stringLength s1))

    subLength :
      (s : CharString) →
      (ofs len : Int) →
      zeroZ ≤Z len →
      zeroZ ≤Z ofs →
      ofs ≤Z stringLength s →
      addInt ofs len ≤Z stringLength s →
      stringLength (stringSub s ofs len) ≡ len

    subIndex :
      (s : CharString) →
      (ofs len i : Int) →
      zeroZ ≤Z len →
      zeroZ ≤Z ofs →
      ofs ≤Z stringLength s →
      addInt ofs len ≤Z stringLength s →
      zeroZ ≤Z i →
      i <Z len →
      stringIndex (stringSub s ofs len) i ≡
      stringIndex s (addInt ofs i)

open StringTheory

StringEqual :
  (S : StringTheory) →
  CharString S →
  CharString S →
  Set
StringEqual S s1 s2 =
  (stringLength S s1 ≡ stringLength S s2) ∧
  ((i : Int) →
   (zeroZ ≤Z i ∧ i <Z stringLength S s1) →
   stringIndex S s1 i ≡ stringIndex S s2 i)

data Rope (S : StringTheory) : Set where
  Emp : Rope S
  Str : CharString S → Int → Int → Rope S
  App : Rope S → Rope S → Int → Rope S

ropeLength : {S : StringTheory} → Rope S → Int
ropeLength Emp = zeroZ
ropeLength (Str _ _ len) = len
ropeLength (App _ _ len) = len

ropeInvariant : {S : StringTheory} → Rope S → Set
ropeInvariant {S} Emp = ⊤
ropeInvariant {S} (Str s ofs len) =
  zeroZ <Z len ∧
  (zeroZ ≤Z ofs ∧ ofs <Z stringLength S s) ∧
  addInt ofs len ≤Z stringLength S s
ropeInvariant {S} (App left right len) =
  zeroZ <Z ropeLength left ∧
  ropeInvariant left ∧
  zeroZ <Z ropeLength right ∧
  ropeInvariant right ∧
  len ≡ addInt (ropeLength left) (ropeLength right)

ropeString :
  {S : StringTheory} →
  Rope S →
  CharString S
ropeString {S} Emp = emptyString S
ropeString {S} (Str s ofs len) = stringSub S s ofs len
ropeString {S} (App left right _) =
  stringApp S (ropeString left) (ropeString right)

record BalanceTheory (S : StringTheory) : Set₁ where
  field
    fib : Int → Int

    fibDefinition :
      (n : Int) →
      zeroZ ≤Z n →
      fib n ≡
      ifInt
        (intEqual n zeroZ)
        zeroZ
        (ifInt
          (intEqual n oneZ)
          oneZ
          (addInt
            (fib (subtractInt n oneZ))
            (fib (subtractInt n twoZ))))

    maximum :
      Int

    maximumDefinition :
      twoZ ≤Z maximum

    stringOfArray :
      List (Rope S) →
      Int →
      Int →
      CharString S

    stringOfArrayEmpty :
      (l : Int) →
      (q : List (Rope S)) →
      zeroZ ≤Z l →
      l ≤Z natToInt (length q) →
      StringEqual S
        (stringOfArray q l l)
        (emptyString S)

    stringOfArrayConcatLeft :
      (l u : Int) →
      (q : List (Rope S)) →
      zeroZ ≤Z l →
      l <Z u →
      u ≤Z natToInt (length q) →
      StringEqual S
        (stringOfArray q l u)
        (stringApp S
          (stringOfArray q (addInt l oneZ) u)
          (ropeString
            (nthDefault Emp (intToNat l) q)))

open BalanceTheory

module InsertStatement
  (S : StringTheory)
  (B : BalanceTheory S)
  where

  ArrayView :
    List (Rope S) →
    Int →
    Rope S
  ArrayView q index =
    nthDefault Emp (intToNat index) q

  updateView :
    (Int → Rope S) →
    Int →
    Rope S →
    Int →
    Rope S
  updateView old key value query with intEqual query key
  ... | true = value
  ... | false = old query

  FunctionEqual :
    (Int → Rope S) →
    (Int → Rope S) →
    Set
  FunctionEqual f g =
    (index : Int) →
    f index ≡ g index

  AllInvariant :
    List (Rope S) →
    Set
  AllInvariant q =
    (j : Int) →
    (twoZ ≤Z j ∧ j ≤Z maximum B) →
    ropeInvariant (ArrayView q j)

  PrefixUnchanged :
    List (Rope S) →
    List (Rope S) →
    Int →
    Set
  PrefixUnchanged q1 q upper =
    (j : Int) →
    (twoZ ≤Z j ∧ j <Z upper) →
    ArrayView q1 j ≡ ArrayView q j

  DirectUpdatePostcondition :
    Int →
    List (Rope S) →
    Rope S →
    Rope S →
    Set
  DirectUpdatePostcondition i q source combined =
    let updated = setAt q (intToNat i) combined
    in
    (zeroZ ≤Z i ∧ i <Z natToInt (length q)) ∧
    (length updated ≡ length q →
     FunctionEqual
       (ArrayView updated)
       (updateView (ArrayView q) i combined) →
     AllInvariant updated ∧
     PrefixUnchanged updated q i ∧
     StringEqual S
       (stringOfArray B
         updated
         i
         (addInt (maximum B) oneZ))
       (stringApp S
         (stringOfArray B
           q
           i
           (addInt (maximum B) oneZ))
         (ropeString source)))

  RecursiveCallPrecondition :
    Int →
    List (Rope S) →
    Rope S →
    Set
  RecursiveCallPrecondition i updated combined =
    let next = addInt i oneZ
    in
    (zeroZ ≤Z subtractInt (maximum B) i ∧
     subtractInt (maximum B) next
       <Z subtractInt (maximum B) i) ∧
    (twoZ ≤Z next ∧
     next <Z natToInt (length updated) ∧
     natToInt (length updated) ≡
       addInt (maximum B) oneZ) ∧
    ropeInvariant combined ∧
    AllInvariant updated ∧
    addInt
      (stringLength S
        (stringOfArray B
          updated
          next
          (addInt (maximum B) oneZ)))
      (ropeLength combined)
      <Z fib B (addInt (maximum B) oneZ)

  RecursiveResultPostcondition :
    Int →
    List (Rope S) →
    List (Rope S) →
    Rope S →
    Rope S →
    Set
  RecursiveResultPostcondition i original updated source combined =
    let next = addInt i oneZ
    in
    (q1 : List (Rope S)) →
    length q1 ≡ length updated →
    (AllInvariant q1 ∧
     PrefixUnchanged q1 updated next ∧
     StringEqual S
       (stringOfArray B
         q1
         next
         (addInt (maximum B) oneZ))
       (stringApp S
         (stringOfArray B
           updated
           next
           (addInt (maximum B) oneZ))
         (ropeString combined))) →
    AllInvariant q1 ∧
    PrefixUnchanged q1 original i ∧
    StringEqual S
      (stringOfArray B
        q1
        i
        (addInt (maximum B) oneZ))
      (stringApp S
        (stringOfArray B
          original
          i
          (addInt (maximum B) oneZ))
        (ropeString source))

  RecursiveBranch :
    Int →
    List (Rope S) →
    Rope S →
    Rope S →
    Set
  RecursiveBranch i q source combined =
    let empty = Emp {S = S}
        updated = setAt q (intToNat i) empty
    in
    (zeroZ ≤Z i ∧ i <Z natToInt (length q)) ∧
    (length updated ≡ length q →
     FunctionEqual
       (ArrayView updated)
       (updateView (ArrayView q) i empty) →
     RecursiveCallPrecondition i updated combined ∧
     RecursiveResultPostcondition i q updated source combined)

  InsertedRopeObligation :
    Int →
    List (Rope S) →
    Rope S →
    Rope S →
    Set
  InsertedRopeObligation i q source combined =
    ropeInvariant combined ∧
    StringEqual S
      (ropeString combined)
      (stringApp S
        (ropeString (ArrayView q i))
        (ropeString source)) →
    let next = addInt i oneZ
    in
    zeroZ ≤Z next ∧
    IfSet
      (intLess (ropeLength combined) (fib B next))
      (DirectUpdatePostcondition i q source combined)
      (RecursiveBranch i q source combined)

  InsertVC :
    Int →
    List (Rope S) →
    Rope S →
    Set
  InsertVC i q source =
    twoZ ≤Z i →
    i <Z natToInt (length q) →
    natToInt (length q) ≡ addInt (maximum B) oneZ →
    ropeInvariant source →
    AllInvariant q →
    addInt
      (stringLength S
        (stringOfArray B
          q
          i
          (addInt (maximum B) oneZ)))
      (ropeLength source)
      <Z fib B (addInt (maximum B) oneZ) →
    (zeroZ ≤Z i ∧ i <Z natToInt (length q)) ∧
    (ropeInvariant (ArrayView q i) ∧ ropeInvariant source) ∧
    ((combined : Rope S) →
     InsertedRopeObligation i q source combined)

insert'vc : Set₁
insert'vc =
  (S : StringTheory) →
  (B : BalanceTheory S) →
  (i : Int) →
  (q : List (Rope S)) →
  (source : Rope S) →
  InsertStatement.InsertVC S B i q source
