-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_b4:
-- n great circles in general position divide the unit sphere into
-- n squared minus n plus two regions. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

NatStrictLess : Nat -> Nat -> Set
NatStrictLess m n =
  suc m <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedField

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

three : Nat
three =
  suc (suc (suc zero))

two : Nat
two =
  suc (suc zero)

Point :
  Set ->
  Set
Point R =
  Fin three -> R

Subset :
  Set ->
  Set1
Subset A =
  A -> Set

record SetEqual
  {A : Set}
  (S T : Subset A) :
  Set where

  constructor same-set
  field
    membership :
      (x : A) ->
      Iff (S x) (T x)

Intersection :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Subset A
Intersection S T x =
  S x and T x

Nonempty :
  {A : Set} ->
  Subset A ->
  Set
Nonempty S =
  Exists _ S

VectorEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
VectorEqual u v =
  (i : Fin three) ->
  u i == v i

ZeroVector :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R
ZeroVector reals i =
  zeroR reals

VectorNonzero :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Set
VectorNonzero reals v =
  Not (VectorEqual v (ZeroVector reals))

dot :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  R
dot reals u v =
  add reals
    (multiply reals (u fzero) (v fzero))
    (add reals
      (multiply reals (u (fsuc fzero)) (v (fsuc fzero)))
      (multiply reals
        (u (fsuc (fsuc fzero)))
        (v (fsuc (fsuc fzero)))))

Sphere :
  {R : Set} ->
  CompleteOrderedField R ->
  Subset (Point R)
Sphere reals x =
  dot reals x x == oneR reals

data Sign : Set where
  negative zeroSign positive : Sign

SignNonzero :
  Sign ->
  Set
SignNonzero sign =
  sign != zeroSign

SignOf :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Sign ->
  Set
SignOf reals x negative =
  StrictLess reals x (zeroR reals)
SignOf reals x zeroSign =
  x == zeroR reals
SignOf reals x positive =
  StrictLess reals (zeroR reals) x

CircleFromNormal :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Subset (Point R)
CircleFromNormal reals normal x =
  Sphere reals x and dot reals normal x == zeroR reals

CircleFamilyInjective :
  {R : Set} ->
  {n : Nat} ->
  (Fin n -> Subset (Point R)) ->
  Set
CircleFamilyInjective C =
  (i j : _) ->
  SetEqual (C i) (C j) ->
  i == j

CirclesThroughPair :
  {R : Set} ->
  {n : Nat} ->
  (Fin n -> Subset (Point R)) ->
  Point R ->
  Point R ->
  Fin n ->
  Set
CirclesThroughPair C x y i =
  C i x and C i y

AtMostTwo :
  {A : Set} ->
  (A -> Set) ->
  Set
AtMostTwo P =
  (i j k : _) ->
  P i ->
  P j ->
  P k ->
  (i == j) or ((i == k) or (j == k))

GeneralPosition :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  (Fin n -> Subset (Point R)) ->
  Set
GeneralPosition reals C =
  (x y : Point _) ->
  Sphere reals x ->
  Sphere reals y ->
  AtMostTwo (CirclesThroughPair C x y)

RegionForSigns :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  (Fin n -> Point R) ->
  (Fin n -> Sign) ->
  Subset (Point R)
RegionForSigns reals normals signs x =
  Sphere reals x
  and
  ((i : _) ->
    SignOf reals (dot reals (normals i) x) (signs i))

RegionsCharacterizedBySigns :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  (Fin n -> Point R) ->
  (Subset (Point R) -> Set) ->
  Set1
RegionsCharacterizedBySigns reals normals IsRegion =
  (region : Subset _) ->
  Iff
    (IsRegion region)
    (Nonempty region
    and
    Exists (Fin _ -> Sign)
      (\ signs ->
        ((i : _) -> SignNonzero (signs i))
        and
        SetEqual region (RegionForSigns reals normals signs)))

record RegionHasCardinality
  {A : Set}
  (IsRegion : Subset A -> Set)
  (count : Nat) :
  Set1 where

  field
    enumerate :
      Fin count -> Subset A
    enumerated-region :
      (i : Fin count) ->
      IsRegion (enumerate i)
    enumeration-complete :
      (region : Subset A) ->
      IsRegion region ->
      Exists (Fin count)
        (\ i -> SetEqual region (enumerate i))
    enumeration-injective :
      (i j : Fin count) ->
      SetEqual (enumerate i) (enumerate j) ->
      i == j

putnam-1964-b4-solution :
  Nat ->
  Nat
putnam-1964-b4-solution n =
  n * n - n + two

putnam-1964-b4 : Set1
putnam-1964-b4 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (n : Nat) ->
  NatStrictLess zero n ->
  (C : Fin n -> Subset (Point R)) ->
  (normals : Fin n -> Point R) ->
  ((i : Fin n) ->
    SetEqual (C i) (CircleFromNormal reals (normals i))) ->
  ((i : Fin n) ->
    VectorNonzero reals (normals i)) ->
  CircleFamilyInjective C ->
  GeneralPosition reals C ->
  (IsRegion : Subset (Point R) -> Set) ->
  RegionsCharacterizedBySigns reals normals IsRegion ->
  RegionHasCardinality IsRegion (putnam-1964-b4-solution n)
