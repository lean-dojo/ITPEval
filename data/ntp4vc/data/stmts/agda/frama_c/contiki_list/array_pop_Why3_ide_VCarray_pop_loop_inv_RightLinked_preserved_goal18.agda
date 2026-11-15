-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/array_pop_Why3_ide_VCarray_pop_loop_inv_RightLinked_preserved_goal18:
-- the right linked-list segment invariant is preserved when an array-backed
-- pointer map is shifted left and one pointer entry is updated under the stated
-- memory-validity, separation, framing, and unchanged-region assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module array_pop_Why3_ide_VCarray_pop_loop_inv_RightLinked_preserved_goal18 where

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

zeroZ oneZ twoZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
fourZ = pos (suc (suc (suc (suc zero))))

maximumArrayIndex signed32Lower signed32Upper : Int
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
PArraySwipeLeft old-memory new-memory array down up =
  (index : Int) →
  down ≤Z index →
  index <Z up →
  new-memory (shift array (addInt oneZ index)) ≡
  old-memory (shift array index)

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
  (linked : (Int → Int) → Set) where

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (base (pointer-memory p)) ≤Z zeroZ

  goal18 : Set
  goal18 =
    (t2 t3 : Addr → Addr) →
    (a4 : Addr) →
    (i2 i : Int) →
    (a1 : Addr) →
    (i3 i1 : Int) →
    (a a3 : Addr) →
    (allocation : Int → Int) →
    (a2 : Addr) →
    (float-memory : Addr → R) →
    let
      a5 = havoc t2 t3 (shift a4 i2) (subtractInt i oneZ)
      a6 = t3 a1
      total = addInt i i2
      next-index = addInt oneZ i3
      right-index = addInt twoZ i3
      array-start = shift a4 zeroZ
      prefix-root = t3 (shift a4 i1)
      prefix-length = subtractInt i2 i1
      root-slot = shift a zeroZ
      updated =
        update a5
          (shift a4 i3)
          (a5 (shift a4 next-index))
    in
    a5 a1 ≡ a6 →
    zeroZ <Z i →
    zeroZ ≤Z i1 →
    i1 ≤Z i2 →
    i2 ≤Z i3 →
    i3 <Z total →
    region (base a) ≤Z zeroZ →
    region (base a1) ≤Z zeroZ →
    region (base a3) ≤Z zeroZ →
    region (base a4) ≤Z zeroZ →
    right-index ≤Z total →
    Framed t3 →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    IsSint32 i2 →
    IsSint32 i3 →
    IsSint32 next-index →
    ValidRW allocation array-start maximumArrayIndex →
    Separated a1 oneZ array-start maximumArrayIndex →
    Separated a6 fourZ array-start maximumArrayIndex →
    PLinkedN allocation t3 a a4 i2 i a3 →
    PLinkedN allocation t3 prefix-root a4 i1 prefix-length a →
    PArraySwipeLeft a5 t3 a4 i2 i3 →
    PLinkedN
      allocation a5 a2 a4 next-index
      (subtractInt (subtractInt (addInt i i2) oneZ) i3)
      a3 →
    PLinkedN allocation a5 prefix-root a4 i1 prefix-length a →
    PLinkedN
      allocation a5 (a5 root-slot) a4 i2
      (subtractInt i3 i2) a2 →
    PUnchanged
      allocation a5 float-memory
      allocation t3 float-memory
      a4 i1 i2 →
    PUnchanged
      allocation a5 float-memory
      allocation t3 float-memory
      a4 i3 total →
    ((index : Int) →
      i1 ≤Z index →
      index <Z total →
      Separated a1 oneZ (t3 (shift a4 index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z total →
      Separated
        (t3 (shift a4 index)) fourZ
        array-start maximumArrayIndex) →
    ((left-index right-index' : Int) →
      left-index ≠ right-index' →
      i1 ≤Z right-index' →
      i1 ≤Z left-index →
      right-index' <Z total →
      left-index <Z total →
      t3 (shift a4 left-index) ≠
      t3 (shift a4 right-index')) →
    ((left-index right-index' : Int) →
      left-index ≠ right-index' →
      i1 ≤Z right-index' →
      i1 ≤Z left-index →
      right-index' <Z total →
      left-index <Z total →
      Separated
        (t3 (shift a4 left-index)) fourZ
        (t3 (shift a4 right-index')) fourZ) →
    PLinkedN
      allocation updated
      (updated (shift a2 zeroZ))
      a4 right-index
      (subtractInt (subtractInt (addInt i i2) twoZ) i3)
      a3

array-pop-loop-invariant-right-linked-preserved-goal18 : Set₂
array-pop-loop-invariant-right-linked-preserved-goal18 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  VC.goal18 {R} region linked
