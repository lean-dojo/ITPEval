-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/koda_ruskey_KodaRuskey_enumqtvc: the Koda-Ruskey enumeration
-- verification condition for recursive forest-stack traversal, coloring
-- updates, and storage of distinct valid solutions. This file contains no proof.

{-# OPTIONS --safe #-}

module koda_ruskey_KodaRuskey_enumqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<Z_ _≤Z_ _≢_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

decideNot : {P : Set} → Dec P → Dec (Not P)
decideNot (yes proof) = no (λ refutation → refutation proof)
decideNot (no refutation) = yes refutation

IfDec : {P : Set} → Dec P → Set → Set → Set
IfDec (yes _) when-true when-false = when-true
IfDec (no _) when-true when-false = when-false

IfBool : Bool → Set → Set → Set
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

FunctionEq :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEq f g = (x : _) → f x ≡ g x

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

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

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
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

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

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

data Color : Set where
  White : Color
  Black : Color

isWhite : Color → Bool
isWhite White = true
isWhite Black = false

data Forest : Set where
  E : Forest
  N : Int → Forest → Forest → Forest

Coloring : Set
Coloring = Int → Color

module Statement (colorDefault : Color) where

  coloringDefault : Coloring
  coloringDefault _ = colorDefault

  colorAt : List Color → Int → Color
  colorAt bits index =
    nthDefault colorDefault (toNat index) bits

  ArrayFunctionEq :
    List Color →
    Coloring →
    Coloring →
    Set
  ArrayFunctionEq bits f g =
    (index : Int) →
    (zeroZ ≤Z index ∧ index <Z lengthZ bits) →
    f index ≡ g index

  coloringAt : List Coloring → Nat → Coloring
  coloringAt colorings index =
    nthDefault coloringDefault index colorings

  updateColoring :
    Coloring →
    Int →
    Color →
    Coloring
  updateColoring old index value query with intEqual query index
  ... | true = value
  ... | false = old query

  sizeForest : Forest → Int
  sizeForest E = zeroZ
  sizeForest (N index leftForest rightForest) =
    addInt
      (addInt oneZ (sizeForest leftForest))
      (sizeForest rightForest)

  memForest : Int → Forest → Set
  memForest sought E = ⊥
  memForest sought (N index leftForest rightForest) =
    index ≡ sought ∨
    memForest sought leftForest ∨
    memForest sought rightForest

  betweenRangeForest : Int → Int → Forest → Set
  betweenRangeForest lower upper forest =
    (index : Int) →
    memForest index forest →
    lower ≤Z index ∧ index <Z upper

  disjoint : Forest → Forest → Set
  disjoint leftForest rightForest =
    (index : Int) →
    memForest index leftForest →
    Not (memForest index rightForest)

  noRepeatedForest : Forest → Set
  noRepeatedForest E = ⊤
  noRepeatedForest (N index leftForest rightForest) =
    noRepeatedForest leftForest ∧
    noRepeatedForest rightForest ∧
    Not (memForest index leftForest) ∧
    Not (memForest index rightForest) ∧
    disjoint leftForest rightForest

  validNumsForest : Forest → Int → Set
  validNumsForest forest count =
    betweenRangeForest zeroZ count forest ∧
    noRepeatedForest forest

  whiteForest : Forest → Coloring → Set
  whiteForest E coloring = ⊤
  whiteForest (N index leftForest rightForest) coloring =
    coloring index ≡ White ∧
    whiteForest leftForest coloring ∧
    whiteForest rightForest coloring

  validColoring : Forest → Coloring → Set
  validColoring E coloring = ⊤
  validColoring (N index leftForest rightForest) coloring
    with coloring index
  ... | White =
    validColoring rightForest coloring ∧
    whiteForest leftForest coloring
  ... | Black =
    validColoring rightForest coloring ∧
    validColoring leftForest coloring

  countForest : Forest → Int
  countForest E = oneZ
  countForest (N index leftForest rightForest) =
    multiplyInt
      (addInt oneZ (countForest leftForest))
      (countForest rightForest)

  eqColoring : Int → Coloring → Coloring → Set
  eqColoring count firstColoring secondColoring =
    (index : Int) →
    zeroZ ≤Z index ∧ index <Z count →
    firstColoring index ≡ secondColoring index

  memStack : Int → List Forest → Set
  memStack sought [] = ⊥
  memStack sought (forest ∷ rest) =
    memForest sought forest ∨ memStack sought rest

  sizeStack : List Forest → Int
  sizeStack [] = zeroZ
  sizeStack (forest ∷ rest) =
    addInt (sizeForest forest) (sizeStack rest)

  evenForest : Forest → Set
  evenForest E = ⊥
  evenForest (N index leftForest rightForest) =
    Not (evenForest leftForest) ∨ evenForest rightForest

  decideEven : (forest : Forest) → Dec (evenForest forest)
  decideEven E = no (λ ())
  decideEven (N index leftForest rightForest)
    with decideNot (decideEven leftForest)
  ... | yes leftNotEven = yes (left leftNotEven)
  ... | no leftNotNotEven with decideEven rightForest
  ...   | yes rightEven = yes (right rightEven)
  ...   | no rightNotEven =
    no λ where
      (left leftNotEven) → leftNotNotEven leftNotEven
      (right rightEven) → rightNotEven rightEven

  finalForest : Forest → Coloring → Set
  finalForest E coloring = ⊤
  finalForest (N index leftForest rightForest) coloring =
    coloring index ≡ Black ∧
    finalForest leftForest coloring ∧
    IfDec
      (decideNot (decideEven leftForest))
      (whiteForest rightForest coloring)
      (finalForest rightForest coloring)

  unchanged :
    List Forest →
    Coloring →
    Coloring →
    Set
  unchanged stack firstColoring secondColoring =
    (index : Int) →
    memStack index stack →
    firstColoring index ≡ secondColoring index

  inverse :
    List Forest →
    Coloring →
    Coloring →
    Set
  inverse [] firstColoring secondColoring = ⊤
  inverse (forest ∷ rest) firstColoring secondColoring =
    ((whiteForest forest firstColoring ∧
      finalForest forest secondColoring) ∨
     (finalForest forest firstColoring ∧
      whiteForest forest secondColoring)) ∧
    IfDec
      (decideEven forest)
      (unchanged rest firstColoring secondColoring)
      (inverse rest firstColoring secondColoring)

  anyStack : List Forest → Coloring → Set
  anyStack [] coloring = ⊤
  anyStack (forest ∷ rest) coloring =
    (whiteForest forest coloring ∨
     finalForest forest coloring) ∧
    anyStack rest coloring

  data Sub : List Forest → Forest → Coloring → Set where
    subReflex :
      (forest : Forest) →
      (coloring : Coloring) →
      Sub (forest ∷ []) forest coloring

    subBrother :
      (stack : List Forest) →
      (rightForest : Forest) →
      (coloring : Coloring) →
      (index : Int) →
      (leftForest : Forest) →
      Sub stack rightForest coloring →
      Sub stack (N index leftForest rightForest) coloring

    subAppend :
      (stack : List Forest) →
      (leftForest : Forest) →
      (coloring : Coloring) →
      (index : Int) →
      (rightForest : Forest) →
      Sub stack leftForest coloring →
      coloring index ≡ Black →
      Sub
        (stack ++ (rightForest ∷ []))
        (N index leftForest rightForest)
        coloring

  countStack : List Forest → Int
  countStack [] = oneZ
  countStack (forest ∷ rest) =
    multiplyInt (countForest forest) (countStack rest)

  storedSolutions :
    Forest →
    Coloring →
    List Forest →
    List Coloring →
    List Coloring →
    Set
  storedSolutions forest bits stack before after =
    let
      count = sizeForest forest
      start = lengthZ before
      stop = lengthZ after
    in
    subtractInt stop start ≡ countStack stack ∧
    ((j : Int) →
      zeroZ ≤Z j ∧ j <Z start →
      eqColoring
        count
        (coloringAt after (toNat j))
        (coloringAt before (toNat j))) ∧
    ((j : Int) →
      start ≤Z j ∧ j <Z stop →
      validColoring forest (coloringAt after (toNat j)) ∧
      ((index : Int) →
        zeroZ ≤Z index ∧ index <Z count →
        Not (memStack index stack) →
        coloringAt after (toNat j) index ≡ bits index) ∧
      ((k : Int) →
        start ≤Z k ∧ k <Z stop →
        j ≢ k →
        Not
          (eqColoring
            count
            (coloringAt after (toNat j))
            (coloringAt after (toNat k)))))

  tailEqual : List Forest → List Forest → Set
  tailEqual [] candidate = ⊥
  tailEqual (_ ∷ rest) candidate = rest ≡ candidate

  decreases :
    List Forest →
    List Forest →
    Set
  decreases oldStack newStack =
    (zeroZ ≤Z sizeStack oldStack ∧
     sizeStack newStack <Z sizeStack oldStack) ∨
    (sizeStack oldStack ≡ sizeStack newStack ∧
     tailEqual oldStack newStack)

  stateInvariant :
    Forest →
    List Color →
    List Forest →
    Set
  stateInvariant initialForest bits stack =
    sizeForest initialForest ≡ lengthZ bits ∧
    validNumsForest initialForest (lengthZ bits) ∧
    Sub stack initialForest (colorAt bits) ∧
    anyStack stack (colorAt bits) ∧
    validColoring initialForest (colorAt bits)

  branchInvariant :
    Forest →
    List Color →
    List Forest →
    List Forest →
    Set
  branchInvariant initialForest bits oldStack newStack =
    decreases oldStack newStack ∧
    stateInvariant initialForest bits newStack

  unchangedOutside :
    List Forest →
    List Color →
    List Color →
    Set
  unchangedOutside stack oldBits newBits =
    (index : Int) →
    Not (memStack index stack) →
    colorAt newBits index ≡ colorAt oldBits index

  transition :
    Forest →
    List Color →
    List Forest →
    List Coloring →
    List Color →
    List Coloring →
    Set
  transition
    initialForest oldBits stack oldVisited newBits newVisited =
      unchangedOutside stack oldBits newBits ∧
      inverse stack (colorAt oldBits) (colorAt newBits) ∧
      validColoring initialForest (colorAt newBits) ∧
      storedSolutions
        initialForest
        (colorAt newBits)
        stack
        oldVisited
        newVisited

  finalTransition :
    Forest →
    List Color →
    List Forest →
    List Coloring →
    List Color →
    List Coloring →
    Set
  finalTransition
    initialForest originalBits originalStack originalVisited
    finalBits finalVisited =
      unchangedOutside originalStack originalBits finalBits ∧
      inverse
        originalStack
        (colorAt originalBits)
        (colorAt finalBits) ∧
      validColoring initialForest (colorAt finalBits) ∧
      storedSolutions
        initialForest
        (colorAt finalBits)
        originalStack
        originalVisited
        finalVisited

  terminalResult :
    Forest →
    List Color →
    List Forest →
    List Coloring →
    List Coloring →
    Set
  terminalResult initialForest bits stack oldVisited newVisited =
    inverse stack (colorAt bits) (colorAt bits) ∧
    validColoring initialForest (colorAt bits) ∧
    storedSolutions
      initialForest
      (colorAt bits)
      stack
      oldVisited
      newVisited

  emptyForestBranch :
    Forest →
    List Color →
    List Coloring →
    Set
  emptyForestBranch initialForest bits visited =
    let
      current = colorAt bits
      extended = visited ++ (current ∷ [])
      stack = E ∷ []
    in
    (lengthZ extended ≡ addInt oneZ (lengthZ visited) ∧
     FunctionEq (coloringAt extended (length visited)) current ∧
     ((index : Int) →
       zeroZ ≤Z index ∧ index <Z lengthZ visited →
       FunctionEq
         (coloringAt extended (toNat index))
         (coloringAt visited (toNat index)))) →
    terminalResult initialForest bits stack visited extended

  nonemptyEmptyForestBranch :
    Forest →
    List Color →
    List Forest →
    List Coloring →
    Set
  nonemptyEmptyForestBranch
    initialForest bits rest visited =
      branchInvariant
        initialForest
        bits
        (E ∷ rest)
        rest ∧
      Not (rest ≡ []) ∧
      ((nextBits : List Color) →
       (nextVisited : List Coloring) →
       length nextBits ≡ length bits →
       transition
         initialForest
         bits
         rest
         visited
         nextBits
         nextVisited →
       finalTransition
         initialForest
         bits
         (E ∷ rest)
         visited
         nextBits
         nextVisited)

  caseTail : List Forest → List Forest
  caseTail [] = []
  caseTail (_ ∷ rest) = rest

  afterWhiteFirstRecursion :
    Forest →
    List Color →
    List Forest →
    List Coloring →
    Int →
    Forest →
    Forest →
    List Color →
    List Coloring →
    Set
  afterWhiteFirstRecursion
    initialForest originalBits originalStack originalVisited
    index leftForest rightForest nextBits nextVisited =
      zeroZ ≤Z index ∧ index <Z lengthZ nextBits ∧
      let
        changedBits = setAt nextBits (toNat index) Black
        nextStack = leftForest ∷ rightForest ∷
          (caseTail originalStack)
      in
      (length changedBits ≡ length nextBits →
       ArrayFunctionEq
         changedBits
         (colorAt changedBits)
         (updateColoring (colorAt nextBits) index Black) →
       branchInvariant
         initialForest
         changedBits
         originalStack
         nextStack ∧
       ((finalBits : List Color) →
        (finalVisited : List Coloring) →
        length finalBits ≡ length changedBits →
        transition
          initialForest
          changedBits
          nextStack
          nextVisited
          finalBits
          finalVisited →
        finalTransition
          initialForest
          originalBits
          originalStack
          originalVisited
          finalBits
          finalVisited))

  afterBlackFirstRecursion :
    Forest →
    List Color →
    List Forest →
    List Coloring →
    Int →
    Forest →
    List Color →
    List Coloring →
    Set
  afterBlackFirstRecursion
    initialForest originalBits originalStack originalVisited
    index rightForest nextBits nextVisited =
      zeroZ ≤Z index ∧ index <Z lengthZ nextBits ∧
      let
        changedBits = setAt nextBits (toNat index) White
        nextStack = rightForest ∷ caseTail originalStack
      in
      (length changedBits ≡ length nextBits →
       ArrayFunctionEq
         changedBits
         (colorAt changedBits)
         (updateColoring (colorAt nextBits) index White) →
       branchInvariant
         initialForest
         changedBits
         originalStack
         nextStack ∧
       ((finalBits : List Color) →
        (finalVisited : List Coloring) →
        length finalBits ≡ length changedBits →
        transition
          initialForest
          changedBits
          nextStack
          nextVisited
          finalBits
          finalVisited →
        finalTransition
          initialForest
          originalBits
          originalStack
          originalVisited
          finalBits
          finalVisited))

  nodeBranch :
    Forest →
    List Color →
    Int →
    Forest →
    Forest →
    List Forest →
    List Coloring →
    Set
  nodeBranch
    initialForest bits index leftForest rightForest rest visited =
      let
        oldStack = N index leftForest rightForest ∷ rest
      in
      zeroZ ≤Z index ∧ index <Z lengthZ bits ∧
      IfBool
        (isWhite (colorAt bits index))
        (let firstStack = rightForest ∷ rest
         in
         branchInvariant
           initialForest bits oldStack firstStack ∧
         ((nextBits : List Color) →
          (nextVisited : List Coloring) →
          length nextBits ≡ length bits →
          transition
            initialForest
            bits
            firstStack
            visited
            nextBits
            nextVisited →
          afterWhiteFirstRecursion
            initialForest bits oldStack visited
            index leftForest rightForest
            nextBits nextVisited))
        (let firstStack = leftForest ∷ rightForest ∷ rest
         in
         branchInvariant
           initialForest bits oldStack firstStack ∧
         ((nextBits : List Color) →
          (nextVisited : List Coloring) →
          length nextBits ≡ length bits →
          transition
            initialForest
            bits
            firstStack
            visited
            nextBits
            nextVisited →
          afterBlackFirstRecursion
            initialForest bits oldStack visited
            index rightForest nextBits nextVisited))

  enumConclusion :
    Forest →
    List Color →
    List Forest →
    List Coloring →
    Set
  enumConclusion initialForest bits [] visited = ⊥
  enumConclusion initialForest bits (E ∷ []) visited =
    emptyForestBranch initialForest bits visited
  enumConclusion
    initialForest bits (E ∷ forest ∷ rest) visited =
      nonemptyEmptyForestBranch
        initialForest bits (forest ∷ rest) visited
  enumConclusion
    initialForest bits (N index leftForest rightForest ∷ rest) visited =
      nodeBranch
        initialForest bits index leftForest rightForest rest visited

  enum'vc : Set
  enum'vc =
    (initialForest : Forest) →
    (bits : List Color) →
    (stack : List Forest) →
    (visited : List Coloring) →
    sizeForest initialForest ≡ lengthZ bits →
    validNumsForest initialForest (lengthZ bits) →
    Sub stack initialForest (colorAt bits) →
    Not (stack ≡ []) →
    anyStack stack (colorAt bits) →
    validColoring initialForest (colorAt bits) →
    enumConclusion initialForest bits stack visited
