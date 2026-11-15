-- Statement-only formalization of PutnamBench corpus artifact putnam_1970_a3:
-- the longest nonzero repeated terminal decimal digit run among perfect
-- squares has length 3, first attained by the square 1444.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; div-helper; mod-helper)

infix 4 _!=_ _<=_ _<_
infixr 3 _and_

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record _×_ (A B : Set) : Set where
  constructor pair
  field
    first-component  : A
    second-component : B

open _×_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

natLess : Nat -> Nat -> Bool
natLess zero zero =
  false
natLess zero (suc n) =
  true
natLess (suc m) zero =
  false
natLess (suc m) (suc n) =
  natLess m n

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

ten : Nat
ten =
  10

digitsWithFuel : Nat -> Nat -> List Nat
digitsWithFuel zero n =
  n ∷ []
digitsWithFuel (suc fuel) n with natLess n ten
... | true =
  n ∷ []
... | false =
  naturalMod n ten ∷
  digitsWithFuel fuel (naturalDiv n ten)

digits : Nat -> List Nat
digits n =
  digitsWithFuel n n

length : {A : Set} -> List A -> Nat
length [] =
  zero
length (x ∷ xs) =
  suc (length xs)

lookupDefault : {A : Set} -> A -> Nat -> List A -> A
lookupDefault default zero [] =
  default
lookupDefault default zero (x ∷ xs) =
  x
lookupDefault default (suc n) [] =
  default
lookupDefault default (suc n) (x ∷ xs) =
  lookupDefault default n xs

digitAt : Nat -> Nat -> Nat
digitAt n k =
  lookupDefault zero k (digits n)

square : Nat -> Nat
square n =
  n * n

three : Nat
three =
  3

putnam-1970-a3-solution : Nat × Nat
putnam-1970-a3-solution =
  pair three 1444

DefinesTerminalRunLength : (Nat -> Nat) -> Set
DefinesTerminalRunLength L =
  (n : Nat) ->
  L n <= length (digits n)
  and
  ((k : Nat) ->
    k < L n ->
    digitAt n k == digitAt n zero)
  and
  (L n != length (digits n) ->
    digitAt n (L n) != digitAt n zero)

putnam-1970-a3 : Set
putnam-1970-a3 =
  (L : Nat -> Nat) ->
  DefinesTerminalRunLength L ->
  Exists Nat
    (\ n ->
      digitAt (square n) zero != zero
      and
      L (square n) == first-component putnam-1970-a3-solution)
  and
  ((n : Nat) ->
    digitAt (square n) zero != zero ->
    L (square n) <= first-component putnam-1970-a3-solution)
  and
  Exists Nat
    (\ m ->
      square m == second-component putnam-1970-a3-solution)
  and
  L (second-component putnam-1970-a3-solution)
    ==
  first-component putnam-1970-a3-solution
  and
  digitAt (second-component putnam-1970-a3-solution) zero != zero
  and
  ((n : Nat) ->
    (digitAt (square n) zero != zero
    and
    L (square n) == first-component putnam-1970-a3-solution) ->
    second-component putnam-1970-a3-solution <= square n)
