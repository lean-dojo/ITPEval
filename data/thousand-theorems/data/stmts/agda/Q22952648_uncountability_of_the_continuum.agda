-- Statement-only formalization of thousand-theorems corpus artifact Q22952648,
-- "Uncountability of the continuum": the real numbers, represented by located
-- Dedekind cuts of the rationals, admit no injection into the natural numbers.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q22952648_uncountability_of_the_continuum where

open import Agda.Primitive using (Level) renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<N_ _<Z_ _<Q_

data Bottom : Set where

data Top : Set where
  trivial : Top

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  constructor both
  field
    first  : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  left  : A -> Either A B
  right : B -> Either A B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a lmax p) where

  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero<successor :
    {n : Nat} ->
    zero <N suc n
  successor<successor :
    {m n : Nat} ->
    m <N n ->
    suc m <N suc n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

scale : Int -> Nat -> Int
scale (pos m) n =
  pos (m * n)
scale (negsuc m) n =
  negative (suc m * n)

_<Z_ : Int -> Int -> Set
pos m <Z pos n =
  m <N n
pos m <Z negsuc n =
  Bottom
negsuc m <Z pos n =
  Top
negsuc m <Z negsuc n =
  n <N m

record Fraction : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Fraction using (numerator; denominator-minus-one)

denominator : Fraction -> Nat
denominator q =
  suc (denominator-minus-one q)

_<Q_ : Fraction -> Fraction -> Set
q <Q r =
  scale (numerator q) (denominator r) <Z
  scale (numerator r) (denominator q)

-- A located lower Dedekind cut is a concrete presentation of a real number.
record DedekindReal : Set₁ where
  field
    lower :
      Fraction -> Set

    inhabited :
      Exists Fraction lower

    proper :
      Exists Fraction (\ q -> Not (lower q))

    downward-closed :
      (q r : Fraction) ->
      q <Q r ->
      lower r ->
      lower q

    rounded :
      (q : Fraction) ->
      Iff
        (lower q)
        (Exists Fraction
          (\ r -> Both (q <Q r) (lower r)))

    located :
      (q r : Fraction) ->
      q <Q r ->
      Either (lower q) (Not (lower r))

open DedekindReal using (lower)

-- Equality of reals is extensional equality of their rational lower cuts.
SameReal : DedekindReal -> DedekindReal -> Set
SameReal x y =
  (q : Fraction) ->
  Iff (lower x q) (lower y q)

InjectiveToNat :
  (DedekindReal -> Nat) ->
  Set₁
InjectiveToNat encode =
  (x y : DedekindReal) ->
  encode x == encode y ->
  SameReal x y

CountableReals : Set₁
CountableReals =
  Exists (DedekindReal -> Nat) InjectiveToNat

uncountability-of-the-continuum : Set₁
uncountability-of-the-continuum =
  Not CountableReals
