-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_b2:
-- coefficient maxima in two real quadratic identities formed from convex
-- linear combinations are at least four ninths. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

maximum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ = y
... | right _ = x

fourN : Nat
fourN =
  suc (suc (suc (suc zero)))

nineN : Nat
nineN =
  suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

module Putnam1967B2Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  oneMinus : R -> R
  oneMinus x =
    subtract reals (oneR reals) x

  fourNinths : R
  fourNinths =
    divide reals (fromNat reals fourN) (fromNat reals nineN)

  firstIdentity :
    R -> R -> R -> R -> R -> Set
  firstIdentity p A B C x =
    (y : R) ->
    square reals
      (add reals
        (multiply reals p x)
        (multiply reals (oneMinus p) y))
    ==
    add reals
      (add reals
        (multiply reals A (square reals x))
        (multiply reals (multiply reals B x) y))
      (multiply reals C (square reals y))

  secondIdentity :
    R -> R -> R -> R -> R -> R -> Set
  secondIdentity p r alpha beta gamma x =
    (y : R) ->
    multiply reals
      (add reals
        (multiply reals p x)
        (multiply reals (oneMinus p) y))
      (add reals
        (multiply reals r x)
        (multiply reals (oneMinus r) y))
    ==
    add reals
      (add reals
        (multiply reals alpha (square reals x))
        (multiply reals (multiply reals beta x) y))
      (multiply reals gamma (square reals y))

  proposition : Set
  proposition =
    (p r A B C alpha beta gamma : R) ->
    (lessOrEqual reals (zeroR reals) p
      and lessOrEqual reals p (oneR reals)
      and lessOrEqual reals (zeroR reals) r
      and lessOrEqual reals r (oneR reals)) ->
    ((x : R) -> firstIdentity p A B C x) ->
    ((x : R) -> secondIdentity p r alpha beta gamma x) ->
    (lessOrEqual reals
      fourNinths
      (maximum reals (maximum reals A B) C))
    and
    (lessOrEqual reals
      fourNinths
      (maximum reals (maximum reals alpha beta) gamma))

putnam-1967-b2 : Set1
putnam-1967-b2 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1967B2Statement.proposition reals
