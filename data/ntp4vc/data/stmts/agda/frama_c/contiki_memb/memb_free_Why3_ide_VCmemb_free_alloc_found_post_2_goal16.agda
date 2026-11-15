-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_alloc_found_post_2_goal16:
-- under the stated index bounds, memory-validity, framing, linkedness,
-- constancy, valid-member, allocation, update, and preceding-search
-- assumptions, freeing the allocated member increases the member pool's
-- free-count by exactly one. This file contains no proof.

{-# OPTIONS --safe #-}

module memb-free-Why3-ide-VCmemb-free-alloc-found-post-2-goal16 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper)

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

truncateDivide : Int → Int → Int
truncateDivide (pos n) (pos zero) = pos zero
truncateDivide (pos n) (pos (suc m)) =
  pos (natDivide n (suc m))
truncateDivide (pos n) (negsuc m) =
  negative (natDivide n (suc m))
truncateDivide (negsuc n) (pos zero) = pos zero
truncateDivide (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))
truncateDivide (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

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

MembIndex :
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Addr →
  Int
MembIndex pointer-memory integer-memory m pointer =
  truncateDivide
    (subtractInt
      (offset pointer)
      (offset (pointer-memory (shift m threeZ))))
    (integer-memory (shift m zeroZ))

MembPtr :
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Int →
  Addr
MembPtr pointer-memory integer-memory m index =
  shift
    (pointer-memory (shift m threeZ))
    (multiplyInt index (integer-memory (shift m zeroZ)))

PHas :
  (Addr → Addr) →
  (Addr → Int) →
  Addr →
  Addr →
  Set
PHas pointer-memory integer-memory m pointer =
  Exists Int λ index →
    MembPtr pointer-memory integer-memory m index ≡ pointer ∧
    zeroZ ≤Z index ∧
    index <Z integer-memory (shift m oneZ)

PAllocated :
  (Addr → Addr) →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Addr →
  Set
PAllocated pointer-memory char-memory integer-memory m pointer =
  char-memory
    (shift
      (pointer-memory (shift m twoZ))
      (MembIndex pointer-memory integer-memory m pointer))
    ≠ zeroZ ∧
  PHas pointer-memory integer-memory m pointer

record OccArrayTheory : Set where
  field
    lOccA : (Addr → Int) → Int → Addr → Int → Int → Int

    end-occ :
      (upper lower : Int) →
      (memory : Addr → Int) →
      (element : Int) →
      (start : Addr) →
      upper ≤Z lower →
      lOccA memory element start lower upper ≡ zeroZ

    iter-occ-true :
      (upper : Int) →
      (memory : Addr → Int) →
      (start : Addr) →
      (element lower : Int) →
      memory (shift start (subtractInt upper oneZ)) ≡ element →
      lower <Z upper →
      addInt oneZ
        (lOccA memory element start lower (subtractInt upper oneZ))
        ≡
      lOccA memory element start lower upper

    iter-occ-false :
      (upper : Int) →
      (memory : Addr → Int) →
      (start : Addr) →
      (element lower : Int) →
      memory (shift start (subtractInt upper oneZ)) ≠ element →
      lower <Z upper →
      lOccA memory element start lower (subtractInt upper oneZ)
        ≡
      lOccA memory element start lower upper

open OccArrayTheory

MembNumFree :
  OccArrayTheory →
  (Addr → Addr) →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int
MembNumFree occurrence-theory pointer-memory char-memory integer-memory m =
  lOccA occurrence-theory
    char-memory
    zeroZ
    (pointer-memory (shift m twoZ))
    zeroZ
    (integer-memory (shift m oneZ))

Goal16 :
  OccArrayTheory →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal16 occurrence-theory region linked sconst =
  (memb : Addr) →
  (integer-memory : Addr → Int) →
  (pointer-memory : Addr → Addr) →
  (found-index : Int) →
  (scan-index : Int) →
  (member-address : Addr) →
  (old-allocation : Int → Int) →
  (old-char-memory : Addr → Int) →
  (new-allocation : Int → Int) →
  (new-char-memory : Addr → Int) →
  let
    count-location = shift memb oneZ
    element-count = integer-memory count-location
    elements-location = shift memb threeZ
    status-location = shift memb twoZ
    found-location =
      shift (pointer-memory status-location) found-index
  in
  MembIndex pointer-memory integer-memory memb
    (MembPtr pointer-memory integer-memory memb scan-index)
    ≡ scan-index →
  zeroZ ≤Z scan-index →
  scan-index ≤Z element-count →
  region (base member-address) ≤Z zeroZ →
  region (base memb) ≤Z zeroZ →
  Framed region pointer-memory →
  linked old-allocation →
  sconst old-char-memory →
  IsSint32 scan-index →
  IsSint32 found-index →
  IsUint16 element-count →
  PValidMemb old-allocation pointer-memory integer-memory memb →
  PHas pointer-memory integer-memory memb member-address →
  ValidRD old-allocation elements-location oneZ →
  ValidRD old-allocation count-location oneZ →
  PAllocated
    pointer-memory old-char-memory integer-memory memb member-address →
  IfSet
    (intLess scan-index element-count)
    (found-index ≡ scan-index ∧
      new-allocation ≈ old-allocation ∧
      MembPtr pointer-memory integer-memory memb found-index
        ≡ member-address ∧
      update old-char-memory found-location zeroZ ≈ new-char-memory ∧
      ValidRD new-allocation status-location oneZ ∧
      ValidRD new-allocation found-location oneZ ∧
      ValidRW new-allocation found-location oneZ)
    (old-char-memory ≈ new-char-memory) →
  ((prior-index : Int) →
    zeroZ ≤Z prior-index →
    prior-index <Z scan-index →
    shift
      (pointer-memory elements-location)
      (multiplyInt
        prior-index
        (integer-memory (shift memb zeroZ)))
      ≠ member-address) →
  addInt oneZ
    (MembNumFree
      occurrence-theory pointer-memory old-char-memory integer-memory memb)
    ≡
  MembNumFree
    occurrence-theory pointer-memory new-char-memory integer-memory memb

memb-free-alloc-found-post-2-goal16 : Set₁
memb-free-alloc-found-post-2-goal16 =
  (occurrence-theory : OccArrayTheory) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal16 occurrence-theory region linked sconst
