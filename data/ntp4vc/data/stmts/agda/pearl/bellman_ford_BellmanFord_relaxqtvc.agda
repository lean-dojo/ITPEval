-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bellman_ford_BellmanFord_relaxqtvc: the Bellman--Ford relaxation
-- verification condition preserving the path-distance invariant after
-- processing one graph edge. This file contains no proof.

{-# OPTIONS --safe #-}

module bellman_ford_BellmanFord_relaxqtvc where

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

record FSet (A : Set) : Set where
  constructor fset
  field
    elements : List A

open FSet

member : {A : Set} → DecEq A → A → FSet A → Set
member dec x set = contains dec x (elements set) ≡ true

insert : {A : Set} → DecEq A → A → FSet A → FSet A
insert dec x set with contains dec x (elements set)
... | true = set
... | false = fset (x ∷ elements set)

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
    Vertex      : Set
    vertexDecEq : DecEq Vertex
    vertices    : FSet Vertex
    edges       : FSet (Pair Vertex Vertex)
    source      : Vertex
    weight      : Vertex → Vertex → Int

    Map      : Set → Set
    contents : {A : Set} → Map A → Vertex → A
    lookup   : {A : Set} → Map A → Vertex → A
    update   : {A : Set} → Map A → Vertex → A → Map A

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

record Laws (sig : Signature) : Set₁ where
  field
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
      (query : Vertex sig) →
      contents sig (update sig map key value) query ≡
        updateValue sig (contents sig map) key value query

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

RelaxVC :
  (sig : Signature) →
  Int →
  Vertex sig →
  Vertex sig →
  FSet (Pair (Vertex sig) (Vertex sig)) →
  Map sig IntInf →
  Set
RelaxVC sig pass u v via map =
  oneZ ≤Z pass →
  member (edgeDecEq sig) (u , v) (edges sig) →
  Not (member (edgeDecEq sig) (u , v) via) →
  inv1 sig map pass via →
  let oldU = lookup sig map u
      candidate = addInf oldU (finite (weight sig u v))
      oldV = lookup sig map v
      via′ = insert (edgeDecEq sig) (u , v) via
  in
  oldU ≡ contents sig map u →
  oldV ≡ contents sig map v →
  IfSet
    (ltInfBool candidate oldV)
    (inv1 sig (update sig map v candidate) pass via′)
    (inv1 sig map pass via′)

relax'vc : (sig : Signature) → Laws sig → Set
relax'vc sig laws =
  (pass : Int) →
  (u v : Vertex sig) →
  (via : FSet (Pair (Vertex sig) (Vertex sig))) →
  (map : Map sig IntInf) →
  RelaxVC sig pass u v via map
