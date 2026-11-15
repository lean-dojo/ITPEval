-- Statement-only formalization of "De Moivre's Theorem" from Hundred Theorems item 017. This
-- file contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Field (C : Set) : Set1 where
  field
    zeroC oneC : C
    add multiply : C -> C -> C
    negate inverse : C -> C
    fromNat : Nat -> C

    one-not-zero :
      oneC != zeroC

    add-commutative :
      (x y : C) -> add x y == add y x
    add-associative :
      (x y z : C) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : C) -> add x zeroC == x
    add-inverse :
      (x : C) -> add x (negate x) == zeroC

    multiply-commutative :
      (x y : C) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : C) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : C) -> multiply x oneC == x
    multiply-zero :
      (x : C) -> multiply x zeroC == zeroC
    distribute :
      (x y z : C) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroC == zeroC
    multiply-inverse :
      (x : C) ->
      x != zeroC ->
      multiply x (inverse x) == oneC

    fromNat-zero :
      fromNat zero == zeroC
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneC
    characteristic-zero :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

open Field

subtract :
  {C : Set} ->
  Field C ->
  C ->
  C ->
  C
subtract algebra x y =
  add algebra x (negate algebra y)

power :
  {C : Set} ->
  Field C ->
  C ->
  Nat ->
  C
power algebra x zero =
  oneC algebra
power algebra x (suc n) =
  multiply algebra x (power algebra x n)

record StandardComplexTrigonometry (C : Set) : Set1 where
  field
    algebra : Field C
    imaginaryUnit : C
    sine cosine : C -> C

    imaginary-unit-square :
      multiply algebra imaginaryUnit imaginaryUnit ==
      negate algebra (oneC algebra)

    sine-zero :
      sine (zeroC algebra) == zeroC algebra
    cosine-zero :
      cosine (zeroC algebra) == oneC algebra
    sine-addition :
      (x y : C) ->
      sine (add algebra x y) ==
      add algebra
        (multiply algebra (sine x) (cosine y))
        (multiply algebra (cosine x) (sine y))
    cosine-addition :
      (x y : C) ->
      cosine (add algebra x y) ==
      subtract algebra
        (multiply algebra (cosine x) (cosine y))
        (multiply algebra (sine x) (sine y))

module Statement
  {C : Set}
  (complex : StandardComplexTrigonometry C) where

  open StandardComplexTrigonometry complex

  cis : C -> C
  cis z =
    add algebra
      (cosine z)
      (multiply algebra imaginaryUnit (sine z))

  proposition : Set
  proposition =
    (z : C) ->
    (n : Nat) ->
    power algebra (cis z) n ==
    cis (multiply algebra (fromNat algebra n) z)

hundred-theorems-017 : Set1
hundred-theorems-017 =
  (C : Set) ->
  (complex : StandardComplexTrigonometry C) ->
  Statement.proposition complex
