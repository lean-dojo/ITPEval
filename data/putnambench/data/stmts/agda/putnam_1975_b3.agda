-- Statement-only formalization of PutnamBench corpus artifact putnam_1975_b3:
-- the elementary-symmetric ratio of finite positive real tuples has supremum
-- 1/k! for every positive natural k. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

open CompleteOrderedRealField

oneN : Nat
oneN =
  suc zero

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

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

record FiniteTuple (R : Set) : Set where
  constructor tuple
  field
    length  : Nat
    entries : Fin length -> R

open FiniteTuple

elementarySymmetric :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Nat ->
  (Fin n -> R) ->
  R
elementarySymmetric reals {zero} zero entries =
  oneR reals
elementarySymmetric reals {zero} (suc k) entries =
  zeroR reals
elementarySymmetric reals {suc n} zero entries =
  oneR reals
elementarySymmetric reals {suc n} (suc k) entries =
  add reals
    (elementarySymmetric reals
      {n}
      (suc k)
      (\ i -> entries (fsuc i)))
    (multiply reals
      (entries fzero)
      (elementarySymmetric reals
        {n}
        k
        (\ i -> entries (fsuc i))))

AllPositive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  FiniteTuple R ->
  Set
AllPositive reals values =
  (i : Fin (length values)) ->
  StrictLess reals
    (zeroR reals)
    (entries values i)

Admissible :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  FiniteTuple R ->
  Set
Admissible reals k values =
  AllPositive reals values
  and
  k <=N length values

elementaryRatio :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  FiniteTuple R ->
  R
elementaryRatio reals k values =
  divide reals
    (elementarySymmetric reals
      k
      (entries values))
    (naturalPower reals
      (elementarySymmetric reals
        oneN
        (entries values))
      k)

putnam-1975-b3-solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
putnam-1975-b3-solution reals k =
  divide reals
    (oneR reals)
    (fromNat reals (factorial k))

IsSpecifiedSupremum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R ->
  Set
IsSpecifiedSupremum {R} reals k supremum =
  ((values : FiniteTuple R) ->
    Admissible reals k values ->
    lessOrEqual reals
      (elementaryRatio reals k values)
      supremum)
  and
  ((lower : R) ->
    StrictLess reals lower supremum ->
    Exists (FiniteTuple R)
      (\ values ->
        Admissible reals k values
        and
        StrictLess reals
          lower
          (elementaryRatio reals k values)))

putnam-1975-b3 : Set1
putnam-1975-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (k : Nat) ->
  oneN <=N k ->
  IsSpecifiedSupremum reals
    k
    (putnam-1975-b3-solution reals k)
