-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bellman_ford_BellmanFord_bellman_fordqtvc: the Bellman--Ford
-- verification condition for its relaxation passes, distance invariants,
-- negative-cycle detection, and final shortest-path specification.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module bellman_ford_BellmanFord_bellman_fordqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

cong :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair

pairDecEq : {A : Set} → DecEq A → DecEq (Pair A A)
pairDecEq dec (a , b) (c , d) with dec a c
... | no a≢c = no (λ equality → a≢c (cong fst equality))
... | yes refl with dec b d
...   | no b≢d = no (λ equality → b≢d (cong snd equality))
...   | yes refl = yes refl

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

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

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

contains : {A : Set} → DecEq A → A → List A → Bool
contains dec x [] = false
contains dec x (y ∷ ys) with dec x y
... | yes _ = true
... | no _ = contains dec x ys

filterAbsent :
  {A : Set} →
  DecEq A →
  List A →
  List A →
  List A
filterAbsent dec [] forbidden = []
filterAbsent dec (x ∷ xs) forbidden with contains dec x forbidden
... | true = filterAbsent dec xs forbidden
... | false = x ∷ filterAbsent dec xs forbidden

removeAll : {A : Set} → DecEq A → A → List A → List A
removeAll dec x [] = []
removeAll dec x (y ∷ ys) with dec x y
... | yes _ = removeAll dec x ys
... | no _ = y ∷ removeAll dec x ys

nub : {A : Set} → DecEq A → List A → List A
nub dec [] = []
nub dec (x ∷ xs) with contains dec x xs
... | true = nub dec xs
... | false = x ∷ nub dec xs

record FSet (A : Set) : Set where
  constructor fset
  field
    elements : List A

open FSet

empty : {A : Set} → FSet A
empty = fset []

member : {A : Set} → DecEq A → A → FSet A → Set
member dec x set = contains dec x (elements set) ≡ true

notMember : {A : Set} → DecEq A → A → FSet A → Set
notMember dec x set = Not (member dec x set)

subset : {A : Set} → DecEq A → FSet A → FSet A → Set
subset {A = A} dec leftSet rightSet =
  (x : A) → member dec x leftSet → member dec x rightSet

setEqual : {A : Set} → DecEq A → FSet A → FSet A → Set
setEqual dec leftSet rightSet =
  subset dec leftSet rightSet ∧ subset dec rightSet leftSet

insert : {A : Set} → DecEq A → A → FSet A → FSet A
insert dec x set with contains dec x (elements set)
... | true = set
... | false = fset (x ∷ elements set)

erase : {A : Set} → DecEq A → A → FSet A → FSet A
erase dec x set = fset (removeAll dec x (elements set))

setDifference : {A : Set} → DecEq A → FSet A → FSet A → FSet A
setDifference dec leftSet rightSet =
  fset (filterAbsent dec (elements leftSet) (elements rightSet))

card : {A : Set} → DecEq A → FSet A → Nat
card dec set = length (nub dec (elements set))

isEmpty : {A : Set} → FSet A → Bool
isEmpty (fset []) = true
isEmpty (fset (_ ∷ _)) = false

nonempty : {A : Set} → FSet A → Set
nonempty set = isEmpty set ≡ false

data IntInf : Set where
  finite   : Int → IntInf
  infinite : IntInf

addInf : IntInf → IntInf → IntInf
addInf infinite _ = infinite
addInf (finite _) infinite = infinite
addInf (finite x) (finite y) = finite (addInt x y)

eqInf : IntInf → IntInf → Set
eqInf infinite infinite = true ≡ true
eqInf (finite x) (finite y) = x ≡ y
eqInf _ _ = false ≡ true

ltInfBool : IntInf → IntInf → Bool
ltInfBool infinite _ = false
ltInfBool (finite _) infinite = true
ltInfBool (finite x) (finite y) = intLess x y

ltInf : IntInf → IntInf → Set
ltInf x y = ltInfBool x y ≡ true

leInf : IntInf → IntInf → Set
leInf x y = ltInf x y ∨ eqInf x y

record Signature : Set₁ where
  field
    Vertex       : Set
    vertexDecEq  : DecEq Vertex
    vertices     : FSet Vertex
    edges        : FSet (Pair Vertex Vertex)
    source       : Vertex
    weight       : Vertex → Vertex → Int

    SetCarrier   : Set
    setDefault   : SetCarrier
    toFSet       : SetCarrier → FSet (Pair Vertex Vertex)
    choose       : SetCarrier → Pair Vertex Vertex

    Map          : Set → Set
    contents     : {A : Set} → Map A → Vertex → A
    create       : {A : Set} → A → Map A
    lookup       : {A : Set} → Map A → Vertex → A
    update       : {A : Set} → Map A → Vertex → A → Map A

open Signature

edgeDecEq : (sig : Signature) → DecEq (Pair (Vertex sig) (Vertex sig))
edgeDecEq sig = pairDecEq (vertexDecEq sig)

edge : (sig : Signature) → Vertex sig → Vertex sig → Set
edge sig x y = member (edgeDecEq sig) (x , y) (edges sig)

data Path
  (sig : Signature) :
  Vertex sig →
  List (Vertex sig) →
  Vertex sig →
  Set where

  pathEmpty :
    (x : Vertex sig) →
    Path sig x [] x

  pathCons :
    (x y z : Vertex sig) →
    (rest : List (Vertex sig)) →
    edge sig x y →
    Path sig y rest z →
    Path sig x (x ∷ rest) z

pathWeight :
  (sig : Signature) →
  List (Vertex sig) →
  Vertex sig →
  Int
pathWeight sig [] destination = zeroZ
pathWeight sig (x ∷ []) destination = weight sig x destination
pathWeight sig (x ∷ y ∷ rest) destination =
  addInt (weight sig x y) (pathWeight sig (y ∷ rest) destination)

listMember :
  (sig : Signature) →
  Vertex sig →
  List (Vertex sig) →
  Set
listMember sig x xs = contains (vertexDecEq sig) x xs ≡ true

allIn :
  (sig : Signature) →
  List (Vertex sig) →
  FSet (Vertex sig) →
  Set
allIn sig xs set =
  (x : Vertex sig) →
  listMember sig x xs →
  member (vertexDecEq sig) x set

repeatedDecomposition :
  (sig : Signature) →
  List (Vertex sig) →
  Set
repeatedDecomposition sig xs =
  Exists (Vertex sig) λ repeated →
  Exists (List (Vertex sig)) λ leftPart →
  Exists (List (Vertex sig)) λ middlePart →
  Exists (List (Vertex sig)) λ rightPart →
  xs ≡
    append leftPart
      (repeated ∷ append middlePart (repeated ∷ rightPart))

pigeonSet :
  (sig : Signature) →
  FSet (Vertex sig) →
  Set
pigeonSet sig set =
  (xs : List (Vertex sig)) →
  allIn sig xs set →
  natLess (card (vertexDecEq sig) set) (length xs) ≡ true →
  repeatedDecomposition sig xs

negativeCycle : (sig : Signature) → Vertex sig → Set
negativeCycle sig v =
  member (vertexDecEq sig) v (vertices sig) ∧
  Exists (List (Vertex sig)) (λ path₁ → Path sig (source sig) path₁ v) ∧
  Exists (List (Vertex sig)) λ path₂ →
    Path sig v path₂ v ∧
    pathWeight sig path₂ v <Z zeroZ

updateValue :
  {A : Set} →
  (sig : Signature) →
  (Vertex sig → A) →
  Vertex sig →
  A →
  Vertex sig →
  A
updateValue sig old key value query with vertexDecEq sig query key
... | yes _ = value
... | no _ = old query

constFunction : {A B : Set} → A → B → A
constFunction value _ = value

record Laws (sig : Signature) : Set₁ where
  field
    chooseSpec :
      (set : SetCarrier sig) →
      nonempty (toFSet sig set) →
      member (edgeDecEq sig) (choose sig set) (toFSet sig set)

    createSpec :
      {A : Set} →
      (x : A) →
      contents sig (create sig x) ≡ constFunction x

    lookupSpec :
      {A : Set} →
      (map : Map sig A) →
      (key : Vertex sig) →
      lookup sig map key ≡ contents sig map key

    updateSpec :
      {A : Set} →
      (map : Map sig A) →
      (key : Vertex sig) →
      (value : A) →
      contents sig (update sig map key value) ≡
        updateValue sig (contents sig map) key value

    edgesWellFormed :
      (x y : Vertex sig) →
      edge sig x y →
      member (vertexDecEq sig) x (vertices sig) ∧
      member (vertexDecEq sig) y (vertices sig)

    sourceInVertices :
      member (vertexDecEq sig) (source sig) (vertices sig)

    pathRightExtension :
      (x y z : Vertex sig) →
      (xs : List (Vertex sig)) →
      Path sig x xs y →
      edge sig y z →
      Path sig x (append xs (y ∷ [])) z

    pathRightInversion :
      (x z : Vertex sig) →
      (xs : List (Vertex sig)) →
      Path sig x xs z →
      ((x ≡ z ∧ xs ≡ []) ∨
       Exists (Vertex sig) λ y →
       Exists (List (Vertex sig)) λ prefix →
         Path sig x prefix y ∧
         edge sig y z ∧
         xs ≡ append prefix (y ∷ []))

    pathTrans :
      (x y z : Vertex sig) →
      (leftPath rightPath : List (Vertex sig)) →
      Path sig x leftPath y →
      Path sig y rightPath z →
      Path sig x (append leftPath rightPath) z

    emptyPath :
      (x y : Vertex sig) →
      Path sig x [] y →
      x ≡ y

    pathDecomposition :
      (x y z : Vertex sig) →
      (leftPath rightPath : List (Vertex sig)) →
      Path sig x (append leftPath (y ∷ rightPath)) z →
      Path sig x leftPath y ∧
      Path sig y (y ∷ rightPath) z

    pathWeightRightExtension :
      (xs : List (Vertex sig)) →
      (x y : Vertex sig) →
      pathWeight sig (append xs (x ∷ [])) y ≡
        addInt (pathWeight sig xs x) (weight sig x y)

    pathWeightDecomposition :
      (leftPath : List (Vertex sig)) →
      (y : Vertex sig) →
      (rightPath : List (Vertex sig)) →
      (z : Vertex sig) →
      pathWeight sig (append leftPath (y ∷ rightPath)) z ≡
        addInt
          (pathWeight sig leftPath y)
          (pathWeight sig (y ∷ rightPath) z)

    pigeonInduction :
      (set : FSet (Vertex sig)) →
      ((candidate : FSet (Vertex sig)) →
       setEqual (vertexDecEq sig) candidate empty →
       pigeonSet sig candidate) →
      ((candidate : FSet (Vertex sig)) →
       pigeonSet sig candidate →
       (x : Vertex sig) →
       pigeonSet sig (insert (vertexDecEq sig) x candidate)) →
      pigeonSet sig set

    corner :
      (xs : List (Vertex sig)) →
      (set : FSet (Vertex sig)) →
      length xs ≡ card (vertexDecEq sig) set →
      allIn sig xs set →
      repeatedDecomposition sig xs ∨
      ((x : Vertex sig) →
       member (vertexDecEq sig) x set →
       listMember sig x xs)

    pigeonZero :
      pigeonSet sig empty

    pigeonOne :
      (set : FSet (Vertex sig)) →
      (x : Vertex sig) →
      pigeonSet sig set →
      pigeonSet sig (insert (vertexDecEq sig) x set)

    pigeonTwo :
      (set : FSet (Vertex sig)) →
      pigeonSet sig set

    pigeonhole :
      (xs : List (Vertex sig)) →
      (set : FSet (Vertex sig)) →
      allIn sig xs set →
      natLess (card (vertexDecEq sig) set) (length xs) ≡ true →
      repeatedDecomposition sig xs

    infimumReflexive :
      (x : IntInf) →
      leInf x x

    infimumTransitive :
      (x y z : IntInf) →
      leInf x y →
      leInf y z →
      leInf x z

    infimumAntisymmetric :
      (x y : IntInf) →
      leInf x y →
      leInf y x →
      x ≡ y

    infimumTotal :
      (x y : IntInf) →
      leInf x y ∨ leInf y x

inv1Case :
  (sig : Signature) →
  Map sig IntInf →
  Int →
  FSet (Pair (Vertex sig) (Vertex sig)) →
  Vertex sig →
  IntInf →
  Set
inv1Case sig map pass via v (finite n) =
  Exists (List (Vertex sig)) (λ xs →
    Path sig (source sig) xs v ∧
    pathWeight sig xs v ≡ n) ∧
  ((xs : List (Vertex sig)) →
    Path sig (source sig) xs v →
    natToInt (length xs) <Z pass →
    n ≤Z pathWeight sig xs v) ∧
  ((u : Vertex sig) →
    (xs : List (Vertex sig)) →
    Path sig (source sig) xs u →
    natToInt (length xs) <Z pass →
    member (edgeDecEq sig) (u , v) via →
    n ≤Z addInt (pathWeight sig xs u) (weight sig u v))
inv1Case sig map pass via v infinite =
  ((xs : List (Vertex sig)) →
    Path sig (source sig) xs v →
    pass ≤Z natToInt (length xs)) ∧
  ((u : Vertex sig) →
    member (edgeDecEq sig) (u , v) via →
    (xs : List (Vertex sig)) →
    Path sig (source sig) xs u →
    pass ≤Z natToInt (length xs))

inv1 :
  (sig : Signature) →
  Map sig IntInf →
  Int →
  FSet (Pair (Vertex sig) (Vertex sig)) →
  Set
inv1 sig map pass via =
  (v : Vertex sig) →
  member (vertexDecEq sig) v (vertices sig) →
  inv1Case sig map pass via v (lookup sig map v)

inv2 :
  (sig : Signature) →
  Map sig IntInf →
  FSet (Pair (Vertex sig) (Vertex sig)) →
  Set
inv2 sig map via =
  (u v : Vertex sig) →
  member (edgeDecEq sig) (u , v) via →
  leInf
    (lookup sig map v)
    (addInf (lookup sig map u) (finite (weight sig u v)))

finalDistanceCase :
  (sig : Signature) →
  Map sig IntInf →
  Vertex sig →
  IntInf →
  Set
finalDistanceCase sig map v (finite n) =
  Exists (List (Vertex sig)) (λ xs →
    Path sig (source sig) xs v ∧
    pathWeight sig xs v ≡ n) ∧
  ((xs : List (Vertex sig)) →
    Path sig (source sig) xs v →
    n ≤Z pathWeight sig xs v)
finalDistanceCase sig map v infinite =
  (xs : List (Vertex sig)) →
  Not (Path sig (source sig) xs v)

allDistancesFinal :
  (sig : Signature) →
  Map sig IntInf →
  Set
allDistancesFinal sig map =
  (v : Vertex sig) →
  member (vertexDecEq sig) v (vertices sig) →
  finalDistanceCase sig map v (lookup sig map v)

decreases :
  (sig : Signature) →
  FSet (Pair (Vertex sig) (Vertex sig)) →
  FSet (Pair (Vertex sig) (Vertex sig)) →
  Set
decreases sig before after =
  zeroZ ≤Z natToInt (card (edgeDecEq sig) before) ∧
  natToInt (card (edgeDecEq sig) after) <Z
    natToInt (card (edgeDecEq sig) before)

relaxPass :
  (sig : Signature) →
  Int →
  Map sig IntInf →
  Set
relaxPass sig index map =
  (es : SetCarrier sig) →
  setEqual (edgeDecEq sig) (toFSet sig es) (edges sig) →
  (subset (edgeDecEq sig) (toFSet sig es) (edges sig) ∧
   inv1 sig map index
     (setDifference (edgeDecEq sig) (edges sig) (toFSet sig es))) ∧
  ((es₁ : SetCarrier sig) →
   (map₂ : Map sig IntInf) →
   subset (edgeDecEq sig) (toFSet sig es₁) (edges sig) ∧
   inv1 sig map₂ index
     (setDifference (edgeDecEq sig) (edges sig) (toFSet sig es₁)) →
   relaxRemaining es₁ map₂)
  where
  relaxRemaining :
    SetCarrier sig →
    Map sig IntInf →
    Set
  relaxRemaining es₁ map₂ =
    IfSet
      (notBool (isEmpty (toFSet sig es₁)))
      (nonempty (toFSet sig es₁) ∧
       ((es₂ : SetCarrier sig) →
        let chosen = choose sig es₁
            via =
              setDifference
                (edgeDecEq sig)
                (edges sig)
                (toFSet sig es₁)
        in
        member (edgeDecEq sig) chosen (toFSet sig es₁) ∧
        setEqual
          (edgeDecEq sig)
          (toFSet sig es₂)
          (erase (edgeDecEq sig) chosen (toFSet sig es₁)) →
        chosenCase chosen via es₂))
      (inv1 sig map₂ (addInt index oneZ) empty)
    where
    chosenCase :
      Pair (Vertex sig) (Vertex sig) →
      FSet (Pair (Vertex sig) (Vertex sig)) →
      SetCarrier sig →
      Set
    chosenCase (u , v) via es₂ =
      ((oneZ ≤Z index ∧
        member (edgeDecEq sig) (u , v) (edges sig) ∧
        notMember (edgeDecEq sig) (u , v) via) ∧
       inv1 sig map₂ index via) ∧
      ((map₃ : Map sig IntInf) →
       inv1 sig map₃ index
         (insert (edgeDecEq sig) (u , v) via) →
       decreases sig (toFSet sig es₁) (toFSet sig es₂) ∧
       subset (edgeDecEq sig) (toFSet sig es₂) (edges sig) ∧
       inv1 sig map₃ index
         (setDifference
           (edgeDecEq sig)
           (edges sig)
           (toFSet sig es₂)))

finalPass :
  (sig : Signature) →
  Map sig IntInf →
  Set
finalPass sig map =
  (es : SetCarrier sig) →
  setEqual (edgeDecEq sig) (toFSet sig es) (edges sig) →
  (subset (edgeDecEq sig) (toFSet sig es) (edges sig) ∧
   inv2 sig map
     (setDifference (edgeDecEq sig) (edges sig) (toFSet sig es))) ∧
  ((es₁ : SetCarrier sig) →
   subset (edgeDecEq sig) (toFSet sig es₁) (edges sig) ∧
   inv2 sig map
     (setDifference (edgeDecEq sig) (edges sig) (toFSet sig es₁)) →
   scanRemaining es₁)
  where
  scanRemaining : SetCarrier sig → Set
  scanRemaining es₁ =
    IfSet
      (notBool (isEmpty (toFSet sig es₁)))
      (nonempty (toFSet sig es₁) ∧
       ((es₂ : SetCarrier sig) →
        let chosen = choose sig es₁
        in
        member (edgeDecEq sig) chosen (toFSet sig es₁) ∧
        setEqual
          (edgeDecEq sig)
          (toFSet sig es₂)
          (erase (edgeDecEq sig) chosen (toFSet sig es₁)) →
        chosenCase chosen es₂))
      (allDistancesFinal sig map)
    where
    chosenCase :
      Pair (Vertex sig) (Vertex sig) →
      SetCarrier sig →
      Set
    chosenCase (u , v) es₂ =
      let oldV = lookup sig map v
          oldU = lookup sig map u
      in
      oldV ≡ contents sig map v →
      oldU ≡ contents sig map u →
      IfSet
        (ltInfBool
          (addInf oldU (finite (weight sig u v)))
          oldV)
        (Exists (Vertex sig) (negativeCycle sig))
        (decreases sig (toFSet sig es₁) (toFSet sig es₂) ∧
         subset (edgeDecEq sig) (toFSet sig es₂) (edges sig) ∧
         inv2 sig map
           (setDifference
             (edgeDecEq sig)
             (edges sig)
             (toFSet sig es₂)))

coreVC : (sig : Signature) → Set
coreVC sig =
  let initialMap =
        update sig
          (create sig infinite)
          (source sig)
          (finite zeroZ)
      lastPass =
        subtractInt
          (natToInt (card (vertexDecEq sig) (vertices sig)))
          oneZ
  in
  (oneZ ≤Z addInt lastPass oneZ →
   inv1 sig initialMap oneZ empty ∧
   ((map₁ : Map sig IntInf) →
    (((index : Int) →
      ((oneZ ≤Z index ∧ index ≤Z lastPass) ∧
       inv1 sig map₁ index empty) →
      relaxPass sig index map₁) ∧
     (inv1 sig map₁ (addInt lastPass oneZ) empty →
      finalPass sig map₁)))) ∧
  (addInt lastPass oneZ <Z oneZ →
   finalPass sig initialMap)

bellman-ford'vc : (sig : Signature) → Laws sig → Set
bellman-ford'vc sig laws = coreVC sig
