-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/isqrt_von_neumann_VonNeumann32_isqrt32qtvc: the 32-bit von Neumann
-- integer-square-root verification condition, including its initialization,
-- loop invariant, conditional update, and final square bounds. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module isqrt_von_neumann_VonNeumann32_isqrt32qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤W_ _<W_
infixr 5 _∷V_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

ifWord : {A : Set} → Bool → A → A → A
ifWord true when-true when-false = when-true
ifWord false when-true when-false = when-false

notBool : Bool → Bool
notBool false = true
notBool true = false

andBit : Bool → Bool → Bool
andBit false _ = false
andBit true y = y

orBit : Bool → Bool → Bool
orBit false y = y
orBit true _ = true

xorBit : Bool → Bool → Bool
xorBit false y = y
xorBit true false = true
xorBit true true = false

bitEqual : Bool → Bool → Bool
bitEqual false false = true
bitEqual false true = false
bitEqual true false = false
bitEqual true true = true

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_  : {n : Nat} → A → Vec A n → Vec A (suc n)

replicate : {A : Set} → (n : Nat) → A → Vec A n
replicate zero value = []V
replicate (suc n) value = value ∷V replicate n value

snoc : {A : Set} {n : Nat} → Vec A n → A → Vec A (suc n)
snoc []V y = y ∷V []V
snoc (x ∷V xs) y = x ∷V snoc xs y

prefix : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
prefix {n = zero} (_ ∷V []V) = []V
prefix {n = suc n} (x ∷V xs) = x ∷V prefix xs

andVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
andVec []V []V = []V
andVec (x ∷V xs) (y ∷V ys) =
  andBit x y ∷V andVec xs ys

orVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
orVec []V []V = []V
orVec (x ∷V xs) (y ∷V ys) =
  orBit x y ∷V orVec xs ys

vecEqual : {n : Nat} → Vec Bool n → Vec Bool n → Bool
vecEqual []V []V = true
vecEqual (x ∷V xs) (y ∷V ys) =
  andBit (bitEqual x y) (vecEqual xs ys)

sumBit : Bool → Bool → Bool → Bool
sumBit carry x y = xorBit (xorBit x y) carry

carryBit : Bool → Bool → Bool → Bool
carryBit carry x y =
  orBit (andBit x y) (andBit carry (xorBit x y))

addWithCarry :
  {n : Nat} →
  Bool →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
addWithCarry carry []V []V = []V
addWithCarry carry (x ∷V xs) (y ∷V ys) =
  sumBit carry x y ∷V
  addWithCarry (carryBit carry x y) xs ys

differenceBit : Bool → Bool → Bool → Bool
differenceBit borrow x y = xorBit (xorBit x y) borrow

borrowBit : Bool → Bool → Bool → Bool
borrowBit borrow x y =
  orBit
    (andBit (notBool x) y)
    (andBit borrow (notBool (xorBit x y)))

subtractWithBorrow :
  {n : Nat} →
  Bool →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
subtractWithBorrow borrow []V []V = []V
subtractWithBorrow borrow (x ∷V xs) (y ∷V ys) =
  differenceBit borrow x y ∷V
  subtractWithBorrow (borrowBit borrow x y) xs ys

bitValue : Bool → Nat
bitValue false = zero
bitValue true = suc zero

unsigned : {n : Nat} → Vec Bool n → Nat
unsigned []V = zero
unsigned (bit ∷V bits) =
  bitValue bit + (suc (suc zero)) * unsigned bits

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

lowBit : Nat → Bool
lowBit zero = false
lowBit (suc zero) = true
lowBit (suc (suc n)) = lowBit n

natToVec : (width value : Nat) → Vec Bool width
natToVec zero value = []V
natToVec (suc width) value =
  lowBit value ∷V natToVec width (half value)

shiftLeftOnce :
  {n : Nat} →
  Vec Bool (suc n) →
  Vec Bool (suc n)
shiftLeftOnce bits = false ∷V prefix bits

shiftLeftNat :
  {n : Nat} →
  Vec Bool (suc n) →
  Nat →
  Vec Bool (suc n)
shiftLeftNat bits zero = bits
shiftLeftNat bits (suc amount) =
  shiftLeftNat (shiftLeftOnce bits) amount

shiftRightOnce :
  {n : Nat} →
  Vec Bool (suc n) →
  Vec Bool (suc n)
shiftRightOnce (_ ∷V bits) = snoc bits false

shiftRightNat :
  {n : Nat} →
  Vec Bool (suc n) →
  Nat →
  Vec Bool (suc n)
shiftRightNat bits zero = bits
shiftRightNat bits (suc amount) =
  shiftRightNat (shiftRightOnce bits) amount

Word32 : Set
Word32 = Vec Bool 32

word : Nat → Word32
word = natToVec 32

zero32 one32 two32 sixteen32 : Word32
zero32 = word 0
one32 = word 1
two32 = word 2
sixteen32 = word 16

thirtyTwoThousandSevenHundredSixtyEight : Word32
thirtyTwoThousandSevenHundredSixtyEight = word 32768

sixtyFiveThousandFiveHundredThirtySix : Word32
sixtyFiveThousandFiveHundredThirtySix = word 65536

oneBillionSeventyThreeMillionSevenHundredFortyOneThousandEightHundredTwentyFour :
  Word32
oneBillionSeventyThreeMillionSevenHundredFortyOneThousandEightHundredTwentyFour =
  word 1073741824

wordEqual : Word32 → Word32 → Bool
wordEqual = vecEqual

wordLeBool : Word32 → Word32 → Bool
wordLeBool x y = natLessOrEqual (unsigned x) (unsigned y)

_≤W_ : Word32 → Word32 → Set
x ≤W y = wordLeBool x y ≡ true

_<W_ : Word32 → Word32 → Set
x <W y = natLess (unsigned x) (unsigned y) ≡ true

wordAdd : Word32 → Word32 → Word32
wordAdd = addWithCarry false

wordSub : Word32 → Word32 → Word32
wordSub = subtractWithBorrow false

wordMul : Word32 → Word32 → Word32
wordMul x y = word (unsigned x * unsigned y)

wordAnd : Word32 → Word32 → Word32
wordAnd = andVec

wordOr : Word32 → Word32 → Word32
wordOr = orVec

wordShiftLeft : Word32 → Word32 → Word32
wordShiftLeft bits amount =
  shiftLeftNat bits (unsigned amount)

wordShiftRight : Word32 → Word32 → Word32
wordShiftRight bits amount =
  shiftRightNat bits (unsigned amount)

sqr : Word32 → Word32
sqr x = wordMul x x

powerOfTwo : Word32 → Word32
powerOfTwo amount = wordShiftLeft one32 amount

isPow2 : Word32 → Word32 → Set
isPow2 x n =
  wordAnd x (wordSub (powerOfTwo n) one32) ≡ zero32

previousPower : Word32 → Word32
previousPower m =
  ifWord
    (wordEqual m zero32)
    zero32
    (powerOfTwo (wordSub m one32))

previousPreviousPower : Word32 → Word32
previousPreviousPower m =
  previousPower (wordSub m one32)

StepFacts : Word32 → Set
StepFacts m =
  let p = previousPower m
  in
  wordShiftRight (sqr p) two32 <W sqr p
  ∧ wordSub m one32 ≤W sixteen32
  ∧ wordShiftRight p one32 ≡ previousPreviousPower m
  ∧ wordShiftRight (sqr p) two32 ≡
      sqr (wordShiftRight p one32)

TakenBranch :
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Set
TakenBranch x res-g m num b =
  let
    p = previousPower m
    next-m = wordSub m one32
    next-res = wordAdd res-g p
    next-place = powerOfTwo next-m
  in
  StepFacts m
  ∧ isPow2 next-res next-m
  ∧ next-res <W sixtyFiveThousandFiveHundredThirtySix
  ∧ wordOr
      (wordShiftRight
        (wordMul res-g (powerOfTwo m))
        one32)
      (sqr p)
      ≡ wordMul next-res next-place
  ∧ wordSub num b ≤W x
  ∧ wordSub x (wordSub num b) ≡ sqr next-res
  ∧ wordAdd next-res next-place ≤W
      sixtyFiveThousandFiveHundredThirtySix
  ∧ x ≤W wordSub
      (sqr (wordAdd next-res next-place))
      one32

UntakenBranch :
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Set
UntakenBranch x res-g m num =
  let
    next-m = wordSub m one32
    next-place = powerOfTwo next-m
  in
  StepFacts m
  ∧ isPow2 res-g next-m
  ∧ res-g <W sixtyFiveThousandFiveHundredThirtySix
  ∧ wordShiftRight
      (wordMul res-g (powerOfTwo m))
      one32
      ≡ wordMul res-g next-place
  ∧ num ≤W x
  ∧ wordSub x num ≡ sqr res-g
  ∧ wordAdd res-g next-place ≤W
      sixtyFiveThousandFiveHundredThirtySix
  ∧ x ≤W wordSub
      (sqr (wordAdd res-g next-place))
      one32

FinishedBranch : Word32 → Word32 → Word32 → Set
FinishedBranch x res-g m =
  let scaled = wordMul res-g (powerOfTwo m)
  in
  sqr scaled ≤W x
  ∧ x ≤W wordSub (sqr (wordAdd scaled one32)) one32

LoopConclusion :
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Set
LoopConclusion x res-g m num =
  let
    p = previousPower m
  in
  IfSet
    (notBool (wordEqual (sqr p) zero32))
    (let
      b = wordOr
        (wordMul res-g (powerOfTwo m))
        (sqr p)
     in
     IfSet
       (wordLeBool b num)
       (TakenBranch x res-g m num b)
       (UntakenBranch x res-g m num))
    (FinishedBranch x res-g m)

LoopInvariant :
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Set
LoopInvariant x res-g m num =
  m ≤W sixteen32
  ∧ isPow2 res-g m
  ∧ res-g <W sixtyFiveThousandFiveHundredThirtySix
  ∧ num ≤W x
  ∧ wordSub x num ≡ sqr res-g
  ∧ wordAdd res-g (powerOfTwo m) ≤W
      sixtyFiveThousandFiveHundredThirtySix
  ∧ x ≤W wordSub
      (sqr (wordAdd res-g (powerOfTwo m)))
      one32

InitialFacts : Word32 → Set
InitialFacts x =
  sixteen32 ≤W sixteen32
  ∧ thirtyTwoThousandSevenHundredSixtyEight ≡
      previousPower sixteen32
  ∧ oneBillionSeventyThreeMillionSevenHundredFortyOneThousandEightHundredTwentyFour
      ≡ sqr thirtyTwoThousandSevenHundredSixtyEight
  ∧ isPow2 zero32 sixteen32
  ∧ zero32 <W sixtyFiveThousandFiveHundredThirtySix
  ∧ zero32 ≡ wordMul zero32 (powerOfTwo sixteen32)
  ∧ x ≤W x
  ∧ wordSub x x ≡ sqr zero32
  ∧ wordAdd zero32 (powerOfTwo sixteen32) ≤W
      sixtyFiveThousandFiveHundredThirtySix
  ∧ x ≤W wordSub
      (sqr (wordAdd zero32 (powerOfTwo sixteen32)))
      one32

isqrt32'vc : Set
isqrt32'vc =
  (x : Word32) →
  InitialFacts x
  ∧
  ((res-g m num : Word32) →
    LoopInvariant x res-g m num →
    LoopConclusion x res-g m num)
