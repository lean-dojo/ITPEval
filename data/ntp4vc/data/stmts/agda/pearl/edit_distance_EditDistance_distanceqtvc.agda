-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/edit_distance_EditDistance_distanceqtvc: the dynamic-programming
-- verification condition establishing a minimal insertion/deletion edit
-- distance for two words through suffix and table invariants. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module edit_distance_EditDistance_distanceqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero

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

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

updateFunction : (Int → Int) → Int → Int → Int → Int
updateFunction old index value query =
  IfInt (intEqual query index) value (old query)

minInt : Int → Int → Int
minInt x y with intLessOrEqual x y
... | true = x
... | false = y

InBounds : {A : Set} → List A → Int → Set
InBounds xs index =
  (zeroZ ≤Z index) ∧ (index <Z lengthZ xs)

BetweenZeroAnd : Int → Int → Set
BetweenZeroAnd index upper =
  (zeroZ ≤Z index) ∧ (index ≤Z upper)

PointwiseEqual : {A B : Set} → (A → B) → (A → B) → Set
PointwiseEqual f g =
  (x : _) → f x ≡ g x

UpdateCondition :
  List Int →
  Int →
  Int →
  Set →
  Set
UpdateCondition xs index value conclusion =
  length (setAt xs (toNat index) value) ≡ length xs →
  PointwiseEqual
    (nthInt (setAt xs (toNat index) value))
    (updateFunction (nthInt xs) index value) →
  conclusion

module EditDistanceTheory
  (Char : Set)
  (charDefault : Char)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (suffix : List Char → Int → List Char)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  IfDec : {P : Set} → Dec P → Set → Set → Set
  IfDec (yes _) when-true when-false = when-true
  IfDec (no _) when-true when-false = when-false

  IfEqual : Char → Char → Set → Set → Set
  IfEqual x y when-equal when-different =
    IfDec (decide (x ≡ y)) when-equal when-different

  nthChar : List Char → Int → Char
  nthChar xs index =
    nthDefault charDefault (toNat index) xs

  data Dist : List Char → List Char → Int → Set where
    dist-eps :
      Dist [] [] zeroZ

    dist-add-left :
      (w1 w2 : List Char) →
      (n : Int) →
      (a : Char) →
      Dist w1 w2 n →
      Dist (a ∷ w1) w2 (addInt n oneZ)

    dist-add-right :
      (w1 w2 : List Char) →
      (n : Int) →
      (a : Char) →
      Dist w1 w2 n →
      Dist w1 (a ∷ w2) (addInt n oneZ)

    dist-context :
      (w1 w2 : List Char) →
      (n : Int) →
      (a : Char) →
      Dist w1 w2 n →
      Dist (a ∷ w1) (a ∷ w2) n

  MinDist : List Char → List Char → Int → Set
  MinDist w1 w2 distance =
    Dist w1 w2 distance ∧
    ((other : Int) → Dist w1 w2 other → distance ≤Z other)

  SuffixLaws : Set
  SuffixLaws =
    ((word : List Char) →
      suffix word (lengthZ word) ≡ []) ∧
    ((index : Int) →
      (word : List Char) →
      zeroZ ≤Z index →
      index <Z lengthZ word →
      suffix word index ≡
        (nthChar word index ∷ suffix word (addInt index oneZ)))

  MinSuffix :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Set
  MinSuffix w1 w2 i j distance =
    MinDist (suffix w1 i) (suffix w2 j) distance

  RowInvariant :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Set
  RowInvariant w1 w2 upper row table =
    (column : Int) →
    BetweenZeroAnd column upper →
    MinSuffix w1 w2 row column (nthInt table column)

  FillPrefix : Int → List Int → Int → Set
  FillPrefix n2 table upper =
    (column : Int) →
    ((zeroZ ≤Z column) ∧ (column <Z upper)) →
    nthInt table column ≡ subtractInt n2 column

  FillStep : Int → List Int → Int → Set
  FillStep n2 table index =
    ((zeroZ ≤Z index) ∧ (index ≤Z n2) ∧
     FillPrefix n2 table index) →
    let value = subtractInt n2 index
        updated = setAt table (toNat index) value
    in
    InBounds table index ∧
    UpdateCondition
      table index value
      (FillPrefix n2 updated (addInt index oneZ))

  FillLoop : Int → List Int → Set
  FillLoop n2 table =
    (index : Int) → FillStep n2 table index

  SplitInvariant :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Int →
    Set
  SplitInvariant w1 w2 n2 currentRow cutoff table oldValue =
    ((column : Int) →
      ((cutoff <Z column) ∧ (column ≤Z n2)) →
      MinSuffix w1 w2 currentRow column (nthInt table column)) ∧
    ((column : Int) →
      BetweenZeroAnd column cutoff →
      MinSuffix
        w1 w2 (addInt currentRow oneZ) column
        (nthInt table column)) ∧
    MinSuffix
      w1 w2 (addInt currentRow oneZ) (addInt cutoff oneZ)
      oldValue

  ColumnState :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    Int →
    List Int →
    Int →
    Set
  ColumnState w1 w2 n2 currentRow lastColumn column table oldValue =
    ((column ≤Z lastColumn) ∧ (zeroZ ≤Z column)) ∧
    ((k : Int) →
      ((column <Z k) ∧ (k ≤Z n2)) →
      MinSuffix w1 w2 currentRow k (nthInt table k)) ∧
    ((k : Int) →
      BetweenZeroAnd k column →
      MinSuffix
        w1 w2 (addInt currentRow oneZ) k
        (nthInt table k)) ∧
    MinSuffix
      w1 w2 (addInt currentRow oneZ) (addInt column oneZ)
      oldValue

  UpdatedCellInvariant :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Int →
    Set
  UpdatedCellInvariant w1 w2 n2 currentRow column table previousCell =
    SplitInvariant
      w1 w2 n2 currentRow (subtractInt column oneZ)
      table previousCell

  CellConclusion :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Int →
    Set
  CellConclusion w1 w2 n2 currentRow column table oldValue =
    InBounds table column ∧
    InBounds w2 column ∧
    InBounds w1 currentRow ∧
    IfEqual
      (nthChar w1 currentRow)
      (nthChar w2 column)
      (InBounds table column ∧
       let updated = setAt table (toNat column) oldValue
       in
       UpdateCondition
         table column oldValue
         (UpdatedCellInvariant
           w1 w2 n2 currentRow column updated
           (nthInt table column)))
      (let nextColumn = addInt column oneZ
       in
       InBounds table nextColumn ∧
       InBounds table column ∧
       (let value =
              addInt
                (minInt
                  (nthInt table column)
                  (nthInt table nextColumn))
                oneZ
            updated = setAt table (toNat column) value
        in
        InBounds table column ∧
        UpdateCondition
          table column value
          (UpdatedCellInvariant
            w1 w2 n2 currentRow column updated
            (nthInt table column))))

  CompletedColumnLoop :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Int →
    Set
  CompletedColumnLoop w1 w2 n2 currentRow table oldValue =
    SplitInvariant
      w1 w2 n2 currentRow minusOneZ table oldValue →
    RowInvariant
      w1 w2 n2
      (addInt (subtractInt currentRow oneZ) oneZ)
      table

  ColumnTables :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Set
  ColumnTables w1 w2 n2 currentRow lastColumn initialTable =
    (oldValue : Int) →
    (table : List Int) →
    length table ≡ length initialTable →
    (((column : Int) →
      ColumnState
        w1 w2 n2 currentRow lastColumn column table oldValue →
      CellConclusion
        w1 w2 n2 currentRow column table oldValue) ∧
     CompletedColumnLoop
       w1 w2 n2 currentRow table oldValue)

  ColumnLoop :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Int →
    Set
  ColumnLoop w1 w2 n2 currentRow lastColumn table previousLastCell =
    SplitInvariant
      w1 w2 n2 currentRow lastColumn table previousLastCell ∧
    ColumnTables
      w1 w2 n2 currentRow lastColumn table

  LastCellUpdate :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Set
  LastCellUpdate w1 w2 n2 currentRow table =
    let value = addInt (nthInt table n2) oneZ
        updated = setAt table (toNat n2) value
        lastColumn = subtractInt n2 oneZ
    in
    InBounds table n2 ∧
    UpdateCondition
      table n2 value
      (((minusOneZ ≤Z lastColumn) →
        ColumnLoop
          w1 w2 n2 currentRow lastColumn updated
          (nthInt table n2)) ∧
       ((lastColumn <Z minusOneZ) →
        RowInvariant
          w1 w2 n2
          (addInt (subtractInt currentRow oneZ) oneZ)
          updated))

  OuterIterationConclusion :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Set
  OuterIterationConclusion w1 w2 n2 currentRow table =
    InBounds table n2 ∧
    InBounds table n2 ∧
    LastCellUpdate w1 w2 n2 currentRow table

  OuterIteration :
    List Char →
    List Char →
    Int →
    Int →
    Int →
    List Int →
    Set
  OuterIteration w1 w2 n2 lastRow currentRow table =
    (((currentRow ≤Z lastRow) ∧ (zeroZ ≤Z currentRow)) ∧
     RowInvariant
       w1 w2 n2 (addInt currentRow oneZ) table) →
    OuterIterationConclusion
      w1 w2 n2 currentRow table

  FinalResult :
    List Char →
    List Char →
    Int →
    List Int →
    Set
  FinalResult w1 w2 n2 table =
    RowInvariant
      w1 w2 n2 (addInt minusOneZ oneZ) table →
    InBounds table zeroZ ∧
    MinDist
      (suffix w1 zeroZ)
      (suffix w2 zeroZ)
      (nthInt table zeroZ)

  NonemptyOuterLoop :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Set
  NonemptyOuterLoop w1 w2 n2 lastRow table =
    RowInvariant
      w1 w2 n2 (addInt lastRow oneZ) table ∧
    ((nextTable : List Int) →
      length nextTable ≡ length table →
      (((currentRow : Int) →
        OuterIteration
          w1 w2 n2 lastRow currentRow nextTable) ∧
       FinalResult w1 w2 n2 nextTable))

  OuterLoop :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Set
  OuterLoop w1 w2 n1 n2 table =
    let lastRow = subtractInt n1 oneZ
    in
    (((minusOneZ ≤Z lastRow) →
      NonemptyOuterLoop w1 w2 n2 lastRow table) ∧
     ((lastRow <Z minusOneZ) →
      InBounds table zeroZ ∧
      MinDist
        (suffix w1 zeroZ)
        (suffix w2 zeroZ)
        (nthInt table zeroZ)))

  PositiveInitialization :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Set
  PositiveInitialization w1 w2 n1 n2 table =
    FillPrefix n2 table zeroZ ∧
    ((filled : List Int) →
      length filled ≡ length table →
      (FillLoop n2 filled ∧
       (FillPrefix n2 filled (addInt n2 oneZ) →
        OuterLoop w1 w2 n1 n2 filled)))

  TableObligations :
    List Char →
    List Char →
    Int →
    Int →
    List Int →
    Set
  TableObligations w1 w2 n1 n2 table =
    ((zeroZ ≤Z addInt n2 oneZ) →
      PositiveInitialization w1 w2 n1 n2 table) ∧
    ((addInt n2 oneZ <Z zeroZ) →
      OuterLoop w1 w2 n1 n2 table)

  DistanceBody : List Char → List Char → Set
  DistanceBody w1 w2 =
    let n1 = lengthZ w1
        n2 = lengthZ w2
        tableLength = addInt n2 oneZ
    in
    (zeroZ ≤Z tableLength) ∧
    ((table : List Int) →
      (((index : Int) →
        ((zeroZ ≤Z index) ∧ (index <Z tableLength)) →
        nthInt table index ≡ zeroZ) ∧
       (lengthZ table ≡ tableLength)) →
      TableObligations w1 w2 n1 n2 table)

  distance-vc : Set
  distance-vc =
    SuffixLaws →
    (w1 w2 : List Char) →
    DistanceBody w1 w2
