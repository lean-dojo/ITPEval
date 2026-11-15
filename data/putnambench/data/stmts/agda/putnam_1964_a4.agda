-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_a4:
-- every bounded integer-valued sequence satisfying the given fourth-order
-- rational recurrence is eventually periodic. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1964A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

NatStrictLess : Nat -> Nat -> Set
NatStrictLess m n =
  suc m <=N n

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
      (m n : Nat) -> fromNat m == fromNat n -> m == n

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
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedField

fromInt :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

four : Nat
four =
  suc (suc (suc (suc zero)))

module Putnam1964A4Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  IntegerValued : (Nat -> R) -> Set
  IntegerValued u =
    (n : Nat) ->
    Exists Int (\ z -> u n == fromInt reals z)

  Bounded : (Nat -> R) -> Set
  Bounded u =
    Exists R
      (\ lower ->
        Exists R
          (\ upper ->
            (n : Nat) ->
            lessOrEqual reals lower (u n)
            and
            lessOrEqual reals (u n) upper))

  numerator : (Nat -> R) -> Nat -> R
  numerator u n =
    add reals
      (add reals
        (u (n - suc zero))
        (u (n - suc (suc zero))))
      (multiply reals
        (u (n - suc (suc (suc zero))))
        (u (n - four)))

  denominator : (Nat -> R) -> Nat -> R
  denominator u n =
    add reals
      (add reals
        (multiply reals
          (u (n - suc zero))
          (u (n - suc (suc zero))))
        (u (n - suc (suc (suc zero)))))
      (u (n - four))

  SatisfiesRecurrence : (Nat -> R) -> Set
  SatisfiesRecurrence u =
    (n : Nat) ->
    four <=N n ->
    (u n == divide reals (numerator u n) (denominator u n))
    and
    denominator u n != zeroR reals

  EventuallyPeriodic : (Nat -> R) -> Set
  EventuallyPeriodic u =
    Exists Nat
      (\ cutoff ->
        Exists Nat
          (\ period ->
            NatStrictLess zero period
            and
            ((n : Nat) ->
              cutoff <=N n ->
              u (n + period) == u n)))

  proposition : Set
  proposition =
    (u : Nat -> R) ->
    Bounded u ->
    SatisfiesRecurrence u ->
    IntegerValued u ->
    EventuallyPeriodic u

putnam-1964-a4 : Set1
putnam-1964-a4 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1964A4Statement.proposition reals
