-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_tail_pre_2_part4_goal33:
-- a linked-list segment remains valid after the specified pointer-memory
-- havoc and null update, under the stated indexing, framing, validity,
-- separation, swipe, unchanged-region, and distinctness assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListAddCallListTailPrePart4Goal33 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

notBool : Bool → Bool
notBool true = false
notBool false = true

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false b = b

ifBool : {A : Set} → Bool → A → A → A
ifBool true yes _ = yes
ifBool false _ no = no

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

zeroZ oneZ twoZ fourZ negativeOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
fourZ = pos (suc (suc (suc (suc zero))))
negativeOneZ = negsuc zero

maximumArrayIndexMinusTwo maximumArrayIndexMinusOne
  maximumArrayIndex signed32Lower signed32Upper : Int
maximumArrayIndexMinusTwo = pos 2147483644
maximumArrayIndexMinusOne = pos 2147483645
maximumArrayIndex = pos 2147483646
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR reciprocalR : R → R
    lessOrEqualR : R → R → Set
    fromNatR : Nat → R

    one-not-zeroR :
      oneR ≠ zeroR

    add-commutativeR :
      (x y : R) → addR x y ≡ addR y x
    add-associativeR :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-zeroR :
      (x : R) → addR x zeroR ≡ x
    add-inverseR :
      (x : R) → addR x (negateR x) ≡ zeroR

    multiply-commutativeR :
      (x y : R) → multiplyR x y ≡ multiplyR y x
    multiply-associativeR :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) → multiplyR x oneR ≡ x
    multiply-zeroR :
      (x : R) → multiplyR x zeroR ≡ zeroR
    distributeR :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR ≡ zeroR
    multiply-reciprocalR :
      (x : R) →
      x ≠ zeroR →
      multiplyR x (reciprocalR x) ≡ oneR

    order-reflexiveR :
      (x : R) → lessOrEqualR x x
    order-transitiveR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR y z →
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) →
      lessOrEqualR x y →
      lessOrEqualR y x →
      x ≡ y
    order-totalR :
      (x y : R) →
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      (lessOrEqualR zeroR oneR) ∧ (zeroR ≠ oneR)

    fromNat-zeroR :
      fromNatR zero ≡ zeroR
    fromNat-successorR :
      (n : Nat) →
      fromNatR (suc n) ≡ addR (fromNatR n) oneR
    fromNat-additionR :
      (m n : Nat) →
      fromNatR (m + n) ≡ addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) →
      fromNatR (m * n) ≡ multiplyR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) →
      fromNatR m ≡ fromNatR n →
      m ≡ n

    archimedeanR :
      (x : R) →
      Exists Nat (λ n → lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) →
          P x →
          lessOrEqualR x upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            P x →
            lessOrEqualR x supremum)
          ∧
          ((upper : R) →
            ((x : R) →
              P x →
              lessOrEqualR x upper) →
            lessOrEqualR supremum upper))

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set₁ where
  field
    forwardR : R → S
    backwardR : S → R
    forward-after-backwardR :
      (y : S) → forwardR (backwardR y) ≡ y
    backward-after-forwardR :
      (x : R) → backwardR (forwardR x) ≡ x
    forward-zeroR :
      forwardR (zeroR source) ≡ zeroR target
    forward-oneR :
      forwardR (oneR source) ≡ oneR target
    forward-addR :
      (x y : R) →
      forwardR (addR source x y) ≡
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) →
      forwardR (multiplyR source x y) ≡
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) →
      forwardR (negateR source x) ≡ negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) →
      forwardR (reciprocalR source x) ≡
      reciprocalR target (forwardR x)
    forward-fromNatR :
      (n : Nat) →
      forwardR (fromNatR source n) ≡ fromNatR target n
    forward-orderR :
      (x y : R) →
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set₂ where
  field
    equivalent-complete-ordered-field :
      (S : Set) →
      (other : CompleteOrderedField S) →
      CompleteOrderedFieldEquivalence reals other

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

addrEqual : Addr → Addr → Bool
addrEqual p q =
  andBool
    (intEqual (base p) (base q))
    (intEqual (offset p) (offset q))

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
update memory location value query =
  ifBool (addrEqual query location) value (memory query)

separatedBool : Addr → Int → Addr → Int → Bool
separatedBool p a q b =
  orBool (intLessOrEqual a zeroZ)
    (orBool (intLessOrEqual b zeroZ)
      (orBool (notBool (intEqual (base p) (base q)))
        (orBool
          (intLessOrEqual (addInt (offset q) b) (offset p))
          (intLessOrEqual (addInt (offset p) a) (offset q)))))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b = separatedBool p a q b ≡ true

havoc :
  (Addr → Addr) →
  (Addr → Addr) →
  Addr →
  Int →
  Addr →
  Addr
havoc old-memory new-memory location size query =
  ifBool
    (separatedBool query oneZ location size)
    (new-memory query)
    (old-memory query)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

record S1List (R : Set) : Set where
  constructor s1list
  field
    next : Addr
    x-coordinate : R
    y-coordinate : R
    z-coordinate : R

open S1List

loadS1List :
  {R : Set} →
  Addr →
  (Addr → R) →
  (Addr → Addr) →
  S1List R
loadS1List p float-memory pointer-memory =
  s1list
    (pointer-memory (shift p zeroZ))
    (float-memory (shift p oneZ))
    (float-memory (shift p twoZ))
    (float-memory (shift p (pos 3)))

EqS1List : {R : Set} → S1List R → S1List R → Set
EqS1List first-list second-list =
  (next second-list ≡ next first-list) ∧
  (x-coordinate second-list ≡ x-coordinate first-list) ∧
  (y-coordinate second-list ≡ y-coordinate first-list) ∧
  (z-coordinate second-list ≡ z-coordinate first-list)

record IndexOfTheory : Set where
  field
    lIndexOf :
      (Addr → Addr) →
      Addr →
      Addr →
      Int →
      Int →
      Int

    no-more-elements :
      (up down : Int) →
      (pointer-memory : Addr → Addr) →
      (item array : Addr) →
      up ≤Z down →
      zeroZ ≤Z up →
      lIndexOf pointer-memory item array down up ≡ up

    found-item :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (down : Int) →
      (item : Addr) →
      (up : Int) →
      pointer-memory (shift array down) ≡ item →
      zeroZ ≤Z down →
      down <Z up →
      lIndexOf pointer-memory item array down up ≡ down

    not-the-item :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (down : Int) →
      (item : Addr) →
      (up : Int) →
      pointer-memory (shift array down) ≠ item →
      zeroZ ≤Z down →
      down <Z up →
      lIndexOf
        pointer-memory item array (addInt oneZ down) up ≡
      lIndexOf pointer-memory item array down up

data PLinkedN :
  (Int → Int) →
  (Addr → Addr) →
  Addr →
  Addr →
  Int →
  Int →
  Addr →
  Set where

  linked-bound :
    (index : Int) →
    (allocation : Int → Int) →
    (pointer-memory : Addr → Addr) →
    (bound array : Addr) →
    zeroZ ≤Z index →
    index ≤Z maximumArrayIndex →
    PLinkedN
      allocation pointer-memory bound array index zeroZ bound

  linked-cons :
    (index n : Int) →
    (pointer-memory : Addr → Addr) →
    (array root : Addr) →
    (allocation : Int → Int) →
    (bound : Addr) →
    pointer-memory (shift array index) ≡ root →
    zeroZ <Z n →
    zeroZ ≤Z index →
    zeroZ ≤Z addInt index n →
    addInt index n ≤Z maximumArrayIndex →
    ValidRW allocation root fourZ →
    PLinkedN
      allocation
      pointer-memory
      (pointer-memory (shift root zeroZ))
      array
      (addInt oneZ index)
      (subtractInt n oneZ)
      bound →
    PLinkedN
      allocation pointer-memory root array index n bound

PArraySwipeLeft :
  (Addr → Addr) →
  (Addr → Addr) →
  Addr →
  Int →
  Int →
  Set
PArraySwipeLeft new-memory old-memory array down up =
  (index : Int) →
  down ≤Z index →
  index <Z up →
  old-memory (shift array (addInt oneZ index)) ≡
  new-memory (shift array index)

PUnchanged :
  {R : Set} →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → R) →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → R) →
  Addr →
  Int →
  Int →
  Set
PUnchanged
  allocation0 pointer-memory0 float-memory0
  allocation1 pointer-memory1 float-memory1
  array down up =
  (index : Int) →
  let
    location = shift array index
    pointer0 = pointer-memory0 location
    pointer1 = pointer-memory1 location
  in
  down ≤Z index →
  index <Z up →
  (pointer0 ≡ pointer1) ∧
  EqS1List
    (loadS1List pointer1 float-memory1 pointer-memory1)
    (loadS1List pointer0 float-memory0 pointer-memory0) ∧
  (ValidRW allocation1 pointer1 fourZ →
   ValidRW allocation0 pointer0 fourZ)

module VC
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (base (pointer-memory p)) ≤Z zeroZ

  goal33 : Set
  goal33 =
    (t3 : Addr → Addr) →
    (a3 : Addr) →
    (i2 i i1 : Int) →
    (t2 : Addr → Addr) →
    (a2 a a1 : Addr) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    let
      a4 = t3 (shift a3 i2)
      x = addInt (addInt oneZ i) i1
      x1 = lIndexOf t3 a4 a3 i1 x
      x2 = subtractInt x1 oneZ
      a5 = shift a3 x2
      a6 = t3 a5
      a7 =
        havoc
          t2
          (update
            (update t3 a2 a)
            (shift a6 zeroZ)
            a1)
          (shift a3 x1)
          (subtractInt x x1)
      a8 = update a7 (shift a4 zeroZ) (addr zeroZ zeroZ)
      a9 = a8 a2
      x3 = addInt i i1
      x4 = addInt oneZ i
      a10 = shift a3 zeroZ
      a11 = t3 a2
      a12 = a7 a2
      found =
        Exists Int
          (λ index →
            (a4 ≡ t3 (shift a3 index)) ∧
            (i1 ≤Z index) ∧
            (index ≤Z x3))
      absent =
        (index : Int) →
        i1 ≤Z index →
        index ≤Z x3 →
        a4 ≠ t3 (shift a3 index)
    in
    a4 ≠ addr zeroZ zeroZ →
    x ≠ x1 →
    a9 ≠ addr zeroZ zeroZ →
    zeroZ ≤Z i1 →
    i1 ≤Z i2 →
    i2 ≤Z x3 →
    region (base a2) ≤Z zeroZ →
    region (base a3) ≤Z zeroZ →
    region (base a4) ≤Z zeroZ →
    i1 ≤Z x1 →
    x1 ≤Z x3 →
    negativeOneZ ≤Z i →
    i ≤Z maximumArrayIndexMinusTwo →
    i1 ≤Z maximumArrayIndexMinusOne →
    x3 ≤Z maximumArrayIndexMinusTwo →
    x1 ≤Z x →
    Framed t3 →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    ValidRW allocation a2 oneZ →
    IsSint32 x4 →
    ValidRW allocation a10 maximumArrayIndex →
    ValidRW allocation (shift a3 i1) x4 →
    ValidRW allocation a4 fourZ →
    Separated a2 oneZ a10 maximumArrayIndex →
    Separated a11 fourZ a10 maximumArrayIndex →
    Separated a2 oneZ a4 fourZ →
    Separated a4 fourZ a10 maximumArrayIndex →
    PLinkedN
      allocation t3 a11 a3 i1 x4 (addr zeroZ zeroZ) →
    IsSint32 x1 →
    Separated a12 fourZ a10 maximumArrayIndex →
    EqS1List
      (loadS1List a4 float-memory a7)
      (loadS1List a4 float-memory t3) →
    (i1 <Z x1 →
      found →
      a7 a5 ≡ a6) →
    (found →
      PArraySwipeLeft a7 t3 a3 x1 x3) →
    (found →
      ((index : Int) →
        i1 ≤Z index →
        index <Z x3 →
        a7 (shift a3 index) ≠ a4)) →
    (absent →
      ((index : Int) →
        i1 ≤Z index →
        index ≤Z x3 →
        a7 (shift a3 index) ≠ a4)) →
    (found →
      PLinkedN
        allocation a7 a12 a3 i1 i
        (addr zeroZ zeroZ)) →
    (absent →
      PLinkedN
        allocation a7 a12 a3 i1 x4
        (addr zeroZ zeroZ)) →
    (absent →
      PUnchanged
        allocation a7 float-memory
        allocation t3 float-memory
        a3 i1 x) →
    (found →
      PUnchanged
        allocation a7 float-memory
        allocation t3 float-memory
        a3 i1 x2) →
    (found →
      ((index : Int) →
        i1 ≤Z index →
        index <Z x3 →
        Separated
          a2 oneZ
          (a7 (shift a3 index)) fourZ)) →
    (absent →
      ((index : Int) →
        i1 ≤Z index →
        index ≤Z x3 →
        Separated
          a2 oneZ
          (a7 (shift a3 index)) fourZ)) →
    (found →
      ((index : Int) →
        i1 ≤Z index →
        index <Z x3 →
        Separated
          a4 fourZ
          (a7 (shift a3 index)) fourZ)) →
    (absent →
      ((index : Int) →
        i1 ≤Z index →
        index ≤Z x3 →
        Separated
          a4 fourZ
          (a7 (shift a3 index)) fourZ)) →
    (found →
      ((index : Int) →
        i1 ≤Z index →
        index <Z x3 →
        Separated
          (a7 (shift a3 index)) fourZ
          a10 maximumArrayIndex)) →
    (absent →
      ((index : Int) →
        i1 ≤Z index →
        index ≤Z x3 →
        Separated
          (a7 (shift a3 index)) fourZ
          a10 maximumArrayIndex)) →
    (found →
      ((index : Int) →
        index <Z x3 →
        x1 ≤Z index →
        EqS1List
          (loadS1List
            (a7 (shift a3 index))
            float-memory
            a7)
          (loadS1List
            (t3 (shift a3 (addInt oneZ index)))
            float-memory
            t3))) →
    (found →
      ((left-index right-index : Int) →
        left-index ≠ right-index →
        i1 ≤Z right-index →
        i1 ≤Z left-index →
        right-index <Z x3 →
        left-index <Z x3 →
        a7 (shift a3 left-index) ≠
        a7 (shift a3 right-index))) →
    (absent →
      ((left-index right-index : Int) →
        left-index ≠ right-index →
        i1 ≤Z right-index →
        i1 ≤Z left-index →
        right-index ≤Z x3 →
        left-index ≤Z x3 →
        a7 (shift a3 left-index) ≠
        a7 (shift a3 right-index))) →
    (found →
      ((left-index right-index : Int) →
        left-index ≠ right-index →
        i1 ≤Z right-index →
        i1 ≤Z left-index →
        right-index <Z x3 →
        left-index <Z x3 →
        Separated
          (a7 (shift a3 left-index)) fourZ
          (a7 (shift a3 right-index)) fourZ)) →
    (absent →
      ((left-index right-index : Int) →
        left-index ≠ right-index →
        i1 ≤Z right-index →
        i1 ≤Z left-index →
        right-index ≤Z x3 →
        left-index ≤Z x3 →
        Separated
          (a7 (shift a3 left-index)) fourZ
          (a7 (shift a3 right-index)) fourZ)) →
    ((index : Int) →
      i1 ≤Z index →
      index ≤Z x3 →
      Separated a2 oneZ (t3 (shift a3 index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index ≤Z x3 →
      Separated
        (t3 (shift a3 index)) fourZ
        a10 maximumArrayIndex) →
    ((index : Int) →
      let pointer = t3 (shift a3 index) in
      a4 ≠ pointer →
      i1 ≤Z index →
      index ≤Z x3 →
      Separated a4 fourZ pointer fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index ≤Z x3 →
      left-index ≤Z x3 →
      t3 (shift a3 left-index) ≠
      t3 (shift a3 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index ≤Z x3 →
      left-index ≤Z x3 →
      Separated
        (t3 (shift a3 left-index)) fourZ
        (t3 (shift a3 right-index)) fourZ) →
    PLinkedN
      allocation a8 a9 a3 i1 i (addr zeroZ zeroZ)

list-add-call-list-tail-pre-part4-goal33 : Set₂
list-add-call-list-tail-pre-part4-goal33 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC.goal33 {R} region linked index-of-theory
