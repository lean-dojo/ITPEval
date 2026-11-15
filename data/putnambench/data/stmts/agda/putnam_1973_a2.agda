-- Statement-only formalization of PutnamBench corpus artifact putnam_1973_a2:
-- convergence of a harmonic series with an eight-periodic pattern of plus and
-- minus signs, and the necessity and sufficiency of four plus signs per period.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1973A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_ _iff_

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

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Top : Set where
  constructor top

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedRealField (R : Set) : Set1 where
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
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
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
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
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

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

data Index8 : Set where
  i0 i1 i2 i3 i4 i5 i6 i7 : Index8

nextIndex : Index8 -> Index8
nextIndex i0 = i1
nextIndex i1 = i2
nextIndex i2 = i3
nextIndex i3 = i4
nextIndex i4 = i5
nextIndex i5 = i6
nextIndex i6 = i7
nextIndex i7 = i0

modEight : Nat -> Index8
modEight zero =
  i0
modEight (suc n) =
  nextIndex (modEight n)

data Sign : Set where
  plus minus : Sign

signValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Sign ->
  R
signValue reals plus =
  oneR reals
signValue reals minus =
  negate reals (oneR reals)

plusCount : Sign -> Nat
plusCount plus =
  suc zero
plusCount minus =
  zero

countPluses : (Index8 -> Sign) -> Nat
countPluses signs =
  plusCount (signs i0) +
  plusCount (signs i1) +
  plusCount (signs i2) +
  plusCount (signs i3) +
  plusCount (signs i4) +
  plusCount (signs i5) +
  plusCount (signs i6) +
  plusCount (signs i7)

four : Nat
four =
  suc (suc (suc (suc zero)))

periodicTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Index8 -> Sign) ->
  Nat ->
  R
periodicTerm reals signs n =
  divide reals
    (signValue reals (signs (modEight n)))
    (fromNat reals n)

partialSums :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Index8 -> Sign) ->
  Nat ->
  R
partialSums reals signs zero =
  zeroR reals
partialSums reals signs (suc n) =
  add reals
    (partialSums reals signs n)
    (periodicTerm reals signs (suc n))

putnam-1973-a2-solution : Set
putnam-1973-a2-solution =
  Top

module Putnam1973A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Converges :
    (Index8 -> Sign) ->
    Set
  Converges signs =
    Exists R
      (\ limit ->
        ConvergesTo reals
          (partialSums reals signs)
          limit)

  proposition : Set
  proposition =
    (signs : Index8 -> Sign) ->
    (pluses : Nat) ->
    pluses == countPluses signs ->
    (pluses == four -> Converges signs)
    and
    (putnam-1973-a2-solution
      iff
      (Converges signs -> pluses == four))

putnam-1973-a2 : Set1
putnam-1973-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1973A2Statement.proposition reals
