-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_memb/memb_init_Why3_ide_VCmemb_init_assert_rte_signed_overflow_2_goal6:
-- under the stated framing, linkedness, constancy, unsigned-integer,
-- valid-member, memory-read, valid-or-empty, and memset assumptions, the
-- member count times the element size does not exceed the signed 32-bit
-- maximum. This file contains no proof.

{-# OPTIONS --safe #-}

module memb-init-Why3-ide-VCmemb-init-assert-rte-signed-overflow-2-goal6 where

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

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false b = b

notBool : Bool → Bool
notBool true = false
notBool false = true

ifBool : {A : Set} → Bool → A → A → A
ifBool true yes _ = yes
ifBool false _ no = no

zeroZ oneZ twoZ threeZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))

uint16Upper signed32Maximum : Int
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

separatedBool : Addr → Int → Addr → Int → Bool
separatedBool p a q b =
  orBool
    (intLessOrEqual a zeroZ)
    (orBool
      (intLessOrEqual b zeroZ)
      (orBool
        (notBool (intEqual (base p) (base q)))
        (orBool
          (intLessOrEqual (addInt (offset q) b) (offset p))
          (intLessOrEqual (addInt (offset p) a) (offset q)))))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b = separatedBool p a q b ≡ true

Havoc :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Addr →
  Int
Havoc old-memory new-memory location size query =
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

ValidRD : (Int → Int) → Addr → Int → Set
ValidRD allocation p n =
  zeroZ <Z n →
  (zeroZ ≠ base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

Framed : (Int → Int) → (Addr → Addr) → Set
Framed region pointer-memory =
  (p : Addr) →
  region (base (pointer-memory p)) ≤Z zeroZ

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

PEmptyBlock : (Int → Int) → Addr → Set
PEmptyBlock allocation block =
  (allocation (base block) ≡ zeroZ) ∧
  (offset block ≡ zeroZ)

PValidOrEmpty : (Int → Int) → Addr → Int → Set
PValidOrEmpty allocation block size =
  ValidRW allocation (shift block zeroZ) size ∧
  Either
    (PEmptyBlock allocation block)
    (ValidRD allocation block oneZ)

LMemset : (Addr → Int) → Addr → Int → Int → Set
LMemset memory block value size =
  (index : Int) →
  zeroZ ≤Z index →
  index <Z size →
  memory (shift block index) ≡ value

Goal6 :
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal6 region linked sconst =
  (a : Addr) →
  (integer-memory : Addr → Int) →
  (pointer-memory : Addr → Addr) →
  (allocation : Int → Int) →
  (new-char-memory : Addr → Int) →
  (old-char-memory : Addr → Int) →
  let
    count-location = shift a oneZ
    element-count = integer-memory count-location
    element-size = integer-memory (shift a zeroZ)
    pointer-location = shift a twoZ
    status-array = pointer-memory pointer-location
  in
  region (base a) ≤Z zeroZ →
  Framed region pointer-memory →
  linked allocation →
  sconst new-char-memory →
  IsUint16 element-count →
  IsUint16 element-size →
  PValidMemb allocation pointer-memory integer-memory a →
  ValidRD allocation pointer-location oneZ →
  ValidRD allocation count-location oneZ →
  PValidOrEmpty allocation status-array element-count →
  LMemset
    (Havoc
      old-char-memory
      new-char-memory
      (shift status-array zeroZ)
      element-count)
    status-array
    zeroZ
    element-count →
  multiplyInt element-count element-size ≤Z signed32Maximum

memb-init-assert-rte-signed-overflow-2-goal6 : Set₁
memb-init-assert-rte-signed-overflow-2-goal6 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal6 region linked sconst
