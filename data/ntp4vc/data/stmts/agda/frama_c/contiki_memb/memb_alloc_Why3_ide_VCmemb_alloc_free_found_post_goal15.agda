-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_goal15:
-- under the stated bounds, memory-validity, framing, linkedness, constancy,
-- valid-member, update, and preceding-occupancy assumptions, there exists an
-- in-range member whose status changes from zero to one, whose element
-- address is returned, and outside which the status memories agree. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module memb-alloc-Why3-ide-VCmemb-alloc-free-found-post-goal15 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_ _≈_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

_≈_ : {A B : Set} → (A → B) → (A → B) → Set
_≈_ {A} f g = (x : A) → f x ≡ g x

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

ifBool : {A : Set} → Bool → A → A → A
ifBool true when-true when-false = when-true
ifBool false when-true when-false = when-false

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

zeroZ oneZ twoZ threeZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))

signed32Lower signed32Upper uint16Upper signed32Maximum : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
uint16Upper = pos 65536
signed32Maximum = pos 2147483647

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

addrEqual : Addr → Addr → Bool
addrEqual (addr base-left offset-left) (addr base-right offset-right) with
  intEqual base-left base-right
... | false = false
... | true = intEqual offset-left offset-right

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
update memory location value query =
  ifBool (addrEqual query location) value (memory query)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

ValidRD : (Int → Int) → Addr → Int → Set
ValidRD allocation p n =
  zeroZ <Z n →
  (zeroZ ≠ base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b =
  Either
    (a ≤Z zeroZ)
    (Either
      (b ≤Z zeroZ)
      (Either
        (base p ≠ base q)
        (Either
          (addInt (offset q) b ≤Z offset p)
          (addInt (offset p) a ≤Z offset q))))

Framed : (Int → Int) → (Addr → Addr) → Set
Framed region pointer-memory =
  (p : Addr) →
  region (base (pointer-memory p)) ≤Z zeroZ

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

IsUint16 : Int → Set
IsUint16 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint16Upper)

PValidMemb :
  (Int → Int) →
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Set
PValidMemb allocation pointer-memory integer-memory m =
  let
    element-size = integer-memory (shift m zeroZ)
    element-count = integer-memory (shift m oneZ)
    total-size = multiplyInt element-count element-size
    status-array = pointer-memory (shift m twoZ)
    elements-array = pointer-memory (shift m threeZ)
    status-start = shift status-array zeroZ
    elements-start = shift elements-array zeroZ
  in
  (zeroZ <Z element-size) ∧
  (total-size ≤Z signed32Maximum) ∧
  ValidRW allocation m fourZ ∧
  ValidRW allocation status-array oneZ ∧
  ValidRW allocation elements-array oneZ ∧
  ValidRW allocation status-start element-count ∧
  ValidRW allocation elements-start total-size ∧
  Separated status-start element-count elements-start total-size

Goal15 :
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal15 region linked sconst =
  (memb : Addr) →
  (pointer-memory : Addr → Addr) →
  (integer-memory : Addr → Int) →
  (found-index : Int) →
  (old-char-memory : Addr → Int) →
  (scan-index : Int) →
  (bound-index : Int) →
  (allocation : Int → Int) →
  (new-char-memory : Addr → Int) →
  (returned-address : Addr) →
  let
    pointer-location = shift memb twoZ
    status-array = pointer-memory pointer-location
    count-location = shift memb oneZ
    element-count = integer-memory count-location
    size-location = shift memb zeroZ
    element-size = integer-memory size-location
    found-location = shift status-array found-index
    elements-location = shift memb threeZ
    elements-array = pointer-memory elements-location
    byte-offset = multiplyInt found-index element-size
  in
  old-char-memory (shift status-array scan-index) ≡ zeroZ →
  zeroZ ≤Z scan-index →
  zeroZ ≤Z bound-index →
  scan-index <Z element-count →
  bound-index ≤Z element-count →
  region (base memb) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  sconst old-char-memory →
  IsSint32 bound-index →
  IsSint32 found-index →
  IsUint16 element-count →
  IsUint16 element-size →
  PValidMemb allocation pointer-memory integer-memory memb →
  ValidRD allocation count-location oneZ →
  IfSet
    (intLess bound-index element-count)
    (found-index ≡ bound-index ∧
      old-char-memory found-location ≡ zeroZ ∧
      update old-char-memory found-location oneZ ≈ new-char-memory ∧
      shift elements-array byte-offset ≡ returned-address ∧
      signed32Lower ≤Z byte-offset ∧
      byte-offset ≤Z signed32Maximum ∧
      ValidRD allocation pointer-location oneZ ∧
      ValidRD allocation elements-location oneZ ∧
      ValidRD allocation size-location oneZ ∧
      ValidRD allocation found-location oneZ ∧
      ValidRW allocation found-location oneZ)
    (old-char-memory ≈ new-char-memory ∧
      addr zeroZ zeroZ ≡ returned-address) →
  ((prior-index : Int) →
    zeroZ ≤Z prior-index →
    prior-index <Z bound-index →
    old-char-memory (shift status-array prior-index) ≠ zeroZ) →
  Exists Int λ member-index →
    let
      member-location = shift status-array member-index
      member-address =
        shift elements-array (multiplyInt member-index element-size)
    in
    new-char-memory member-location ≡ oneZ ∧
    old-char-memory member-location ≡ zeroZ ∧
    member-address ≡ returned-address ∧
    zeroZ ≤Z member-index ∧
    member-index <Z element-count ∧
    ((other-index : Int) →
      let other-location = shift status-array other-index
      in
      Either
        (zeroZ ≤Z other-index ∧ other-index <Z member-index)
        (member-index <Z other-index ∧ other-index <Z element-count) →
      old-char-memory other-location ≡ new-char-memory other-location)

memb-alloc-free-found-post-goal15 : Set₁
memb-alloc-free-found-post-goal15 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal15 region linked sconst
