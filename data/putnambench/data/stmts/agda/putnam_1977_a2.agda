-- Statement-only formalization of PutnamBench corpus artifact putnam_1977_a2:
-- the nonzero real solutions of the sum and reciprocal-sum equations are
-- exactly the three symmetric cancellation families. This file has no proof.

{-# OPTIONS --safe #-}

module Putnam1977A2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _!=_
infixr 3 _and_

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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data ThreeWays (A B C : Set) : Set where
  first-way  : A -> ThreeWays A B C
  second-way : B -> ThreeWays A B C
  third-way  : C -> ThreeWays A B C

data Choice (A B : Set) : Set where
  choose-left  : A -> Choice A B
  choose-right : B -> Choice A B

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
      multiply x (add y z) == add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) -> x != zeroR -> multiply x (inverse x) == oneR

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
      (x y : R) -> Choice (lessOrEqual x y) (lessOrEqual y x)
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
      (m n : Nat) -> fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) -> Σ Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Σ R P ->
      Σ R (\ upper -> (x : R) -> P x -> lessOrEqual x upper) ->
      Σ R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y = multiply reals x (inverse reals y)

module Putnam1977A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  equations : R -> R -> R -> R -> Set
  equations a b c d =
    (add reals (add reals a b) c == d)
    and
    (add reals
      (add reals
        (divide reals (oneR reals) a)
        (divide reals (oneR reals) b))
      (divide reals (oneR reals) c)
      ==
      divide reals (oneR reals) d)

  solutions : R -> R -> R -> R -> Set
  solutions a b c d =
    ThreeWays
      ((d == a) and (b == negate reals c))
      ((d == b) and (a == negate reals c))
      ((d == c) and (a == negate reals b))

  proposition : Set
  proposition =
    (a b c d : R) ->
    (a != zeroR reals)
    and
    ((b != zeroR reals)
    and
    ((c != zeroR reals) and (d != zeroR reals))) ->
    Iff (equations a b c d) (solutions a b c d)

putnam-1977-a2 : Set1
putnam-1977-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1977A2Statement.proposition reals
