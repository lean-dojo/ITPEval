-- Statement-only formalization of PutnamBench corpus artifact putnam_1989_a6:
-- the binary-digit formal power series over the field with two elements
-- satisfies alpha cubed plus X times alpha plus one equals zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; _-_; div-helper; mod-helper)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {A : Set}
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumeration-complete :
      (x : A) ->
      Exists (Fin cardinality)
        (\ index -> enumerate index == x)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record Field (F : Set) : Set1 where
  field
    zeroF oneF : F
    add multiply : F -> F -> F
    negate inverse : F -> F

    one-not-zero :
      oneF != zeroF

    add-commutative :
      (x y : F) ->
      add x y == add y x
    add-associative :
      (x y z : F) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : F) ->
      add x zeroF == x
    add-inverse :
      (x : F) ->
      add x (negate x) == zeroF

    multiply-commutative :
      (x y : F) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : F) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : F) ->
      multiply x oneF == x
    multiply-zero :
      (x : F) ->
      multiply x zeroF == zeroF
    distribute :
      (x y z : F) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroF == zeroF
    multiply-inverse :
      (x : F) ->
      x != zeroF ->
      multiply x (inverse x) == oneF

open Field

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

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

append : {A : Set} -> List A -> List A -> List A
append [] right =
  right
append (x ∷ left) right =
  x ∷ append left right

binaryDigitsWithFuel : Nat -> Nat -> List Nat
binaryDigitsWithFuel zero n =
  []
binaryDigitsWithFuel (suc fuel) zero =
  []
binaryDigitsWithFuel (suc fuel) (suc n) =
  naturalMod (suc n) twoN ∷
  binaryDigitsWithFuel fuel (naturalDiv (suc n) twoN)

binaryDigits : Nat -> List Nat
binaryDigits zero =
  []
binaryDigits (suc n) =
  binaryDigitsWithFuel (suc n) (suc n)

toggle : Bool -> Bool
toggle false =
  true
toggle true =
  false

evenZeroBlocksFrom : Bool -> List Nat -> Bool
evenZeroBlocksFrom parity [] =
  true
evenZeroBlocksFrom parity (zero ∷ digits) =
  evenZeroBlocksFrom (toggle parity) digits
evenZeroBlocksFrom false (suc digit ∷ digits) =
  evenZeroBlocksFrom false digits
evenZeroBlocksFrom true (suc digit ∷ digits) =
  false

augmentedBinaryDigits : Nat -> List Nat
augmentedBinaryDigits n =
  oneN ∷ append (binaryDigits n) (oneN ∷ [])

everyZeroBlockEven : Nat -> Bool
everyZeroBlockEven n =
  evenZeroBlocksFrom false (augmentedBinaryDigits n)

PowerSeries : Set -> Set
PowerSeries F =
  Nat -> F

SeriesEqual :
  {F : Set} ->
  PowerSeries F ->
  PowerSeries F ->
  Set
SeriesEqual left right =
  (n : Nat) ->
  left n == right n

seriesZero :
  {F : Set} ->
  Field F ->
  PowerSeries F
seriesZero algebra n =
  zeroF algebra

seriesOne :
  {F : Set} ->
  Field F ->
  PowerSeries F
seriesOne algebra zero =
  oneF algebra
seriesOne algebra (suc n) =
  zeroF algebra

seriesX :
  {F : Set} ->
  Field F ->
  PowerSeries F
seriesX algebra zero =
  zeroF algebra
seriesX algebra (suc zero) =
  oneF algebra
seriesX algebra (suc (suc n)) =
  zeroF algebra

seriesAdd :
  {F : Set} ->
  Field F ->
  PowerSeries F ->
  PowerSeries F ->
  PowerSeries F
seriesAdd algebra left right n =
  add algebra (left n) (right n)

sumThrough :
  {F : Set} ->
  Field F ->
  Nat ->
  (Nat -> F) ->
  F
sumThrough algebra zero term =
  term zero
sumThrough algebra (suc n) term =
  add algebra
    (sumThrough algebra n term)
    (term (suc n))

seriesMultiply :
  {F : Set} ->
  Field F ->
  PowerSeries F ->
  PowerSeries F ->
  PowerSeries F
seriesMultiply algebra left right n =
  sumThrough algebra n
    (\ k ->
      multiply algebra
        (left k)
        (right (n - k)))

seriesPower :
  {F : Set} ->
  Field F ->
  PowerSeries F ->
  Nat ->
  PowerSeries F
seriesPower algebra series zero =
  seriesOne algebra
seriesPower algebra series (suc n) =
  seriesMultiply algebra
    (seriesPower algebra series n)
    series

coefficientValue :
  {F : Set} ->
  Field F ->
  Nat ->
  F
coefficientValue algebra n with everyZeroBlockEven n
... | false =
  zeroF algebra
... | true =
  oneF algebra

CoefficientSpecification :
  {F : Set} ->
  Field F ->
  PowerSeries F ->
  Set
CoefficientSpecification algebra alpha =
  (n : Nat) ->
  alpha n == coefficientValue algebra n

formalEquation :
  {F : Set} ->
  Field F ->
  PowerSeries F ->
  Set
formalEquation algebra alpha =
  SeriesEqual
    (seriesAdd algebra
      (seriesAdd algebra
        (seriesPower algebra alpha threeN)
        (seriesMultiply algebra
          (seriesX algebra)
          alpha))
      (seriesOne algebra))
    (seriesZero algebra)

putnam-1989-a6 : Set1
putnam-1989-a6 =
  (F : Set) ->
  (algebra : Field F) ->
  HasCardinality {A = F} twoN ->
  (alpha : PowerSeries F) ->
  CoefficientSpecification algebra alpha ->
  formalEquation algebra alpha
