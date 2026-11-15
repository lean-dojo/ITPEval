-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linear_probing_LinearProbing_memqtvc: the verification condition for
-- membership probing in a linear-probing hash table, including nonempty-table,
-- free-slot, probe-prefix, and view-membership obligations. This file contains no proof.

{-# OPTIONS --safe #-}

module linear_probing_LinearProbing_memqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

IfNat : Bool → Nat → Nat → Nat
IfNat true when-true when-false = when-true
IfNat false when-true when-false = when-false

natModFuel : Nat → Nat → Nat → Nat
natModFuel zero dividend divisor = dividend
natModFuel (suc fuel) dividend zero = dividend
natModFuel (suc fuel) dividend (suc divisor) =
  IfNat
    (natLess dividend (suc divisor))
    dividend
    (natModFuel
      fuel
      (natSubtract dividend (suc divisor))
      (suc divisor))

natMod : Nat → Nat → Nat
natMod dividend divisor =
  natModFuel (suc dividend) dividend divisor

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

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

tmodInt : Int → Int → Int
tmodInt (pos n) divisor =
  pos (natMod n (absoluteNat divisor))
tmodInt (negsuc n) divisor =
  negative (natMod (suc n) (absoluteNat divisor))

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

countFrom : (Int → Bool) → Int → Nat → Nat
countFrom predicate start zero = zero
countFrom predicate start (suc count) with predicate start
... | true =
  suc (countFrom predicate (addInt start oneZ) count)
... | false =
  countFrom predicate (addInt start oneZ) count

numOf : (Int → Bool) → Int → Int → Int
numOf predicate lower upper =
  natToInt
    (countFrom predicate lower (toNat (subtractInt upper lower)))

module LinearProbingMemTheory
  (Key KeyM T : Set)
  (dummy : Key)
  (keym : Key → KeyM)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (hash : Key → Int)
  (size : T → Int)
  (entriesOf : T → List Key)
  (view : T → KeyM → Bool)
  (loc : T → KeyM → Int)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  eq : Key → Key → Set
  eq x y = keym x ≡ keym y

  neq : Key → Key → Set
  neq x y = Not (eq x y)

  equalKeyM : KeyM → KeyM → Bool
  equalKeyM x y with decide (x ≡ y)
  ... | yes _ = true
  ... | no _ = false

  nthKey : List Key → Int → Key
  nthKey xs index = nthDefault dummy (toNat index) xs

  bucket : Key → Int → Int
  bucket k n = tmodInt (hash k) n

  between : Int → Int → Int → Set
  between l j r =
    (l ≤Z j ∧ j <Z r)
    ∨ (r <Z l ∧ l ≤Z j)
    ∨ (j <Z r ∧ r <Z l)

  fc : List Key → Int → Bool
  fc xs i = equalKeyM (keym (nthKey xs i)) (keym dummy)

  numof : List Key → Int → Int → Int
  numof xs lower upper = numOf (fc xs) lower upper

  InRange : List Key → Int → Set
  InRange entries i =
    zeroZ ≤Z i ∧ i <Z lengthZ entries

  valid :
    List Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  valid entries present location =
    Not (present (keym dummy) ≡ true)
    ∧
    ((i : Int) →
      InRange entries i →
      let x = nthKey entries i
      in
      neq x dummy →
      present (keym x) ≡ true ∧
      location (keym x) ≡ i)
    ∧
    (let n = lengthZ entries
     in
     (x : Key) →
     present (keym x) ≡ true →
     let i = location (keym x)
     in
     InRange entries i
     ∧ eq (nthKey entries i) x
     ∧
     ((j : Int) →
       InRange entries j →
       between (bucket x n) j i →
       neq (nthKey entries j) x ∧
       neq (nthKey entries j) dummy))

  StateInvariant :
    Int →
    List Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  StateInvariant stateSize entries present location =
    zeroZ ≤Z stateSize
    ∧ stateSize <Z lengthZ entries
    ∧ addInt stateSize (numof entries zeroZ (lengthZ entries))
        ≡ lengthZ entries
    ∧ valid entries present location

  FunctionEqual :
    {A B : Set} →
    (A → B) →
    (A → B) →
    Set
  FunctionEqual f g = (x : _) → f x ≡ g x

  StateEqual : T → T → Set
  StateEqual a b =
    size a ≡ size b
    ∧ entriesOf a ≡ entriesOf b
    ∧ FunctionEqual (view a) (view b)
    ∧ FunctionEqual (loc a) (loc b)

  record Laws : Set where
    field
      hash-nonnegative :
        (k : Key) →
        zeroZ ≤Z hash k

      hash-respects-eq :
        (x y : Key) →
        eq x y →
        hash x ≡ hash y

      bucket-range :
        (n : Int) →
        (k : Key) →
        zeroZ <Z n →
        zeroZ ≤Z bucket k n ∧ bucket k n <Z n

      state-invariant :
        (self : T) →
        StateInvariant
          (size self)
          (entriesOf self)
          (view self)
          (loc self)

      state-injective :
        (a b : T) →
        StateEqual a b →
        a ≡ b

  ProbePrefix :
    Key →
    List Key →
    Int →
    Set
  ProbePrefix x entries i =
    (j : Int) →
    InRange entries j →
    between (bucket x (lengthZ entries)) j i →
    neq (nthKey entries j) x ∧
    neq (nthKey entries j) dummy

  MemConclusion :
    Key →
    T →
    Set
  MemConclusion x h =
    let o1 = dummy
        o2 = entriesOf h
    in
    (neq x dummy
     ∧
     (let n = lengthZ o2
      in zeroZ <Z n ∧ zeroZ <Z numof o2 zeroZ n))
    ∧
    ((o3 : Int) →
      (InRange o2 o3
       ∧ (eq (nthKey o2 o3) dummy ∨ eq (nthKey o2 o3) x)
       ∧ ProbePrefix x o2 o3) →
      let o4 = entriesOf h
      in
      InRange o4 o3
      ∧
      (let o5 = nthKey o4 o3
       in
       (neq o5 o1 ↔ Not (keym o5 ≡ keym o1)) →
       (neq o5 o1 ↔ view h (keym x) ≡ true)))

  MemVC :
    Laws →
    Key →
    T →
    Set
  MemVC laws x h =
    neq x dummy →
    MemConclusion x h

  mem-vc : Set
  mem-vc =
    (laws : Laws) →
    (x : Key) →
    (h : T) →
    MemVC laws x h
