-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/hillel_challenge_FulcrumNoOverflow_fulcrumqtvc: a fulcrum-search
-- verification condition preserving signed 32-bit array bounds, exact prefix
-- and suffix sums, minimum-difference invariants, and accumulator overflow
-- bounds. This file contains no proof.

{-# OPTIONS --safe #-}

module hillel_challenge_FulcrumNoOverflow_fulcrumqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_

data Unit : Set where
  unit : Unit

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

absoluteInt : Int → Int
absoluteInt (pos n) = pos n
absoluteInt (negsuc n) = pos (suc n)

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

bitValue : Bool → Nat
bitValue false = zero
bitValue true = suc zero

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + (suc (suc zero)) * unsignedNat bits

lastBit : {n : Nat} → Vec Bool (suc n) → Bool
lastBit {zero} (bit ∷V []V) = bit
lastBit {suc n} (_ ∷V bits) = lastBit bits

Word32 : Set
Word32 = Vec Bool 32

signed : Word32 → Int
signed bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true = subtractInt (pos (unsignedNat bits)) (pos 4294967296)

zeroZ oneZ fiftyFiveZ eightyNineZ baseZ max32Z min32Z : Int
zeroZ = pos 0
oneZ = pos 1
fiftyFiveZ = pos 55
eightyNineZ = pos 89
baseZ = pos 2147483648
max32Z = pos 2147483647
min32Z = negsuc 2147483647

max32Word : Word32
max32Word = natToVec 32 2147483647

int32InBounds : Int → Set
int32InBounds x = min32Z ≤Z x ∧ x ≤Z max32Z

wideInBounds : Int → Set
wideInBounds x =
  negateInt (multiplyInt baseZ baseZ) ≤Z x ∧
  x ≤Z subtractInt (multiplyInt baseZ baseZ) oneZ

BigInvariantFor :
  {Big : Set} →
  (Big → Word32) →
  (Big → Word32) →
  (Big → Int) →
  Big →
  Set
BigInvariantFor q r v self =
  min32Z ≤Z signed (q self) ∧
  signed (q self) ≤Z max32Z ∧
  zeroZ ≤Z signed (r self) ∧
  signed (r self) ≤Z max32Z ∧
  v self ≡
    addInt
      (multiplyInt (signed (q self)) baseZ)
      (signed (r self))

BigEqualFor :
  {Big : Set} →
  (Big → Word32) →
  (Big → Word32) →
  (Big → Int) →
  Big →
  Big →
  Set
BigEqualFor q r v a b =
  q a ≡ q b ∧ r a ≡ r b ∧ v a ≡ v b

record Context : Set₁ where
  field
    Array32 : Set → Set
    array32Elts :
      {A : Set} →
      Array32 A →
      Int →
      A
    array32Length :
      {A : Set} →
      Array32 A →
      Word32

    intSum : (Int → Int) → Int → Int → Int
    intSum-def :
      (b a : Int) →
      (f : Int → Int) →
      IfSet
        (intLessOrEqual b a)
        (intSum f a b ≡ zeroZ)
        (intSum f a b ≡
          addInt
            (intSum f a (subtractInt b oneZ))
            (f (subtractInt b oneZ)))
    intSum-left :
      (a b : Int) →
      (f : Int → Int) →
      a <Z b →
      intSum f a b ≡
        addInt (f a) (intSum f (addInt a oneZ) b)
    intSum-ext :
      (a b : Int) →
      (f g : Int → Int) →
      ((i : Int) →
        (a ≤Z i ∧ i <Z b) →
        f i ≡ g i) →
      intSum f a b ≡ intSum g a b
    intSum-le :
      (a b : Int) →
      (f g : Int → Int) →
      ((i : Int) →
        (a ≤Z i ∧ i <Z b) →
        f i ≤Z g i) →
      intSum f a b ≤Z intSum g a b
    intSum-zero :
      (a b : Int) →
      (f : Int → Int) →
      ((i : Int) →
        (a ≤Z i ∧ i <Z b) →
        f i ≡ zeroZ) →
      intSum f a b ≡ zeroZ
    intSum-nonnegative :
      (a b : Int) →
      (f : Int → Int) →
      ((i : Int) →
        (a ≤Z i ∧ i <Z b) →
        zeroZ ≤Z f i) →
      zeroZ ≤Z intSum f a b
    intSum-decompose :
      (a b c : Int) →
      (f : Int → Int) →
      a ≤Z b →
      b ≤Z c →
      intSum f a c ≡ addInt (intSum f a b) (intSum f b c)
    intSum-shift-left :
      (b a d c : Int) →
      (f g : Int → Int) →
      subtractInt b a ≡ subtractInt d c →
      ((i : Int) →
        (a ≤Z i ∧ i <Z b) →
        f i ≡ g (subtractInt (addInt c i) a)) →
      intSum f a b ≡ intSum g c d

    Big : Set
    q : Big → Word32
    r : Big → Word32
    v : Big → Int
    big-invariant :
      (self : Big) →
      BigInvariantFor q r v self
    big-injective :
      (a b : Big) →
      BigEqualFor q r v a b →
      a ≡ b
    big-zero : Unit → Big
    big-zero-def :
      (x : Unit) →
      q (big-zero x) ≡ natToVec 32 0 ∧
      r (big-zero x) ≡ natToVec 32 0 ∧
      v (big-zero x) ≡ zeroZ

module FulcrumStatement (ctx : Context) where

  open Context ctx

  Array : Set
  Array = Array32 Word32

  fc : Array → Int → Int
  fc a i = signed (array32Elts a i)

  sum : Array → Int → Int → Int
  sum a lower upper = intSum (fc a) lower upper

  diff : Array → Int → Int
  diff a i =
    absoluteInt
      (subtractInt
        (sum a zeroZ i)
        (sum a i (signed (array32Length a))))

  goodConstant : Set
  goodConstant = fiftyFiveZ <Z eightyNineZ

  indexInArray : Array → Word32 → Set
  indexInArray a i =
    zeroZ ≤Z signed i ∧
    signed i <Z signed (array32Length a)

  integerRange : Int → Int → Set
  integerRange value upper =
    zeroZ ≤Z value ∧ value ≤Z upper

  bigInvariant : Big → Set
  bigInvariant = BigInvariantFor q r v

  runningInvariant :
    Array →
    Word32 →
    Big →
    Word32 →
    Big →
    Big →
    Int →
    Set
  runningInvariant a n bestd besti left right boundary =
    goodConstant ∧
    v left ≡ sum a zeroZ boundary ∧
    v right ≡ sum a boundary (signed n) ∧
    integerRange (signed besti) boundary ∧
    v bestd ≡ diff a (signed besti) ∧
    ((j : Int) →
      integerRange j boundary →
      v bestd ≤Z diff a j)

  initialInvariant :
    Array →
    Word32 →
    Big →
    Big →
    Big →
    Set
  initialInvariant a n left right bestd =
    goodConstant ∧
    v left ≡ sum a zeroZ zeroZ ∧
    v right ≡ sum a zeroZ (signed n) ∧
    zeroZ ≤Z zeroZ ∧
    v bestd ≡ diff a zeroZ ∧
    ((j : Int) →
      integerRange j zeroZ →
      v bestd ≤Z diff a j)

  improvementCase :
    Array →
    Word32 →
    Word32 →
    Int →
    Big →
    Word32 →
    Big →
    Big →
    Big →
    Set
  improvementCase
    a n i i1 bestd1 besti left3 right3 d =
      IfSet
        (intLess (v d) (v bestd1))
        ((bestd2 : Big) →
          int32InBounds (addInt (signed i) oneZ) ∧
          ((o5 : Word32) →
            signed o5 ≡ addInt (signed i) oneZ →
            bigInvariant d ∧
            ((v d ≡ v bestd2 ∧
              r d ≡ r bestd2 ∧
              q d ≡ q bestd2) →
              runningInvariant
                a n bestd2 o5 left3 right3
                (addInt i1 oneZ))))
        (runningInvariant
          a n bestd1 besti left3 right3
          (addInt i1 oneZ))

  differenceStep :
    Array →
    Word32 →
    Word32 →
    Int →
    Big →
    Word32 →
    Big →
    Big →
    Set
  differenceStep
    a n i i1 bestd1 besti left3 right3 =
      (d : Big) →
      v d ≡ absoluteInt (subtractInt (v left3) (v right3)) →
      (zeroZ ≤Z v d ∧ zeroZ ≤Z v bestd1) ∧
      improvementCase
        a n i i1 bestd1 besti left3 right3 d

  rightUpdateStep :
    Array →
    Word32 →
    Word32 →
    Int →
    Big →
    Word32 →
    Big →
    Big →
    Set
  rightUpdateStep
    a n i i1 bestd1 besti left3 right2 =
      let o4 = array32Elts a (signed i)
      in
      wideInBounds
        (subtractInt (v right2) (signed o4)) ∧
      ((right3 : Big) →
        v right3 ≡
          subtractInt (v right2) (signed o4) →
        wideInBounds
          (absoluteInt
            (subtractInt (v left3) (v right3))) ∧
        differenceStep
          a n i i1 bestd1 besti left3 right3)

  leftUpdateStep :
    Array →
    Word32 →
    Word32 →
    Int →
    Big →
    Word32 →
    Big →
    Big →
    Set
  leftUpdateStep a n i i1 bestd1 besti left2 right2 =
    let o3 = array32Elts a (signed i)
    in
    wideInBounds (addInt (v left2) (signed o3)) ∧
    ((left3 : Big) →
      v left3 ≡ addInt (v left2) (signed o3) →
      indexInArray a i ∧
      rightUpdateStep
        a n i i1 bestd1 besti left3 right2)

  secondLoopStep :
    Array →
    Word32 →
    Word32 →
    Big →
    Word32 →
    Big →
    Big →
    Set
  secondLoopStep a n o2 bestd1 besti left2 right2 =
    (i : Word32) →
    let i1 = signed i
    in
    (integerRange i1 (signed o2) ∧
     runningInvariant
       a n bestd1 besti left2 right2 i1) →
    indexInArray a i ∧
    leftUpdateStep
      a n i i1 bestd1 besti left2 right2

  secondLoopPackage :
    Array →
    Word32 →
    Word32 →
    Big →
    Word32 →
    Big →
    Big →
    Set
  secondLoopPackage a n o2 bestd1 besti left2 right2 =
    secondLoopStep
      a n o2 bestd1 besti left2 right2 ∧
    (runningInvariant
      a n bestd1 besti left2 right2
      (addInt (signed o2) oneZ) →
      integerRange
        (signed besti)
        (signed (array32Length a)) ∧
      ((i : Int) →
        integerRange i (signed (array32Length a)) →
        diff a (signed besti) ≤Z diff a i))

  negativeSecondLoop :
    Array →
    Set
  negativeSecondLoop a =
    (zeroZ ≤Z zeroZ ∧
     zeroZ ≤Z signed (array32Length a)) ∧
    ((i : Int) →
      integerRange i (signed (array32Length a)) →
      diff a zeroZ ≤Z diff a i)

  finishSearch :
    Array →
    Word32 →
    Big →
    Set
  finishSearch a n right =
    let left = big-zero unit
    in
    wideInBounds
      (absoluteInt (subtractInt (v left) (v right))) ∧
    ((bestd : Big) →
      v bestd ≡
        absoluteInt (subtractInt (v left) (v right)) →
      int32InBounds (subtractInt (signed n) oneZ) ∧
      ((o2 : Word32) →
        signed o2 ≡ subtractInt (signed n) oneZ →
        ((zeroZ ≤Z addInt (signed o2) oneZ →
          initialInvariant a n left right bestd ∧
          ((bestd1 : Big) →
            (besti : Word32) →
            (left2 right2 : Big) →
            secondLoopPackage
              a n o2 bestd1 besti left2 right2)) ∧
         (addInt (signed o2) oneZ <Z zeroZ →
          negativeSecondLoop a))))

  firstLoopStep :
    Array →
    Word32 →
    Big →
    Set
  firstLoopStep a o1 right2 =
    (i : Word32) →
    let i1 = signed i
    in
    (integerRange i1 (signed o1) ∧
     goodConstant ∧
     v right2 ≡ sum a zeroZ i1) →
    indexInArray a i ∧
    (let o2 = array32Elts a (signed i)
     in
     wideInBounds (addInt (v right2) (signed o2)) ∧
     ((right3 : Big) →
       v right3 ≡ addInt (v right2) (signed o2) →
       goodConstant ∧
       v right3 ≡ sum a zeroZ (addInt i1 oneZ)))

  firstLoopPackage :
    Array →
    Word32 →
    Word32 →
    Big →
    Set
  firstLoopPackage a n o1 right2 =
    firstLoopStep a o1 right2 ∧
    ((goodConstant ∧
      v right2 ≡
        sum a zeroZ (addInt (signed o1) oneZ)) →
      finishSearch a n right2)

  FulcrumVC : Array → Set
  FulcrumVC a =
    signed (array32Length a) <Z signed max32Word →
    let n = array32Length a
        right1 = big-zero unit
    in
    int32InBounds (subtractInt (signed n) oneZ) ∧
    ((o1 : Word32) →
      signed o1 ≡ subtractInt (signed n) oneZ →
      ((zeroZ ≤Z addInt (signed o1) oneZ →
        (goodConstant ∧
         v right1 ≡ sum a zeroZ zeroZ) ∧
        ((right2 : Big) →
          firstLoopPackage a n o1 right2)) ∧
       (addInt (signed o1) oneZ <Z zeroZ →
        finishSearch a n right1)))

fulcrum'vc : (ctx : Context) → Set
fulcrum'vc ctx =
  (a : FulcrumStatement.Array ctx) →
  FulcrumStatement.FulcrumVC ctx a
