-- Statement-only formalization of thousand-theorems corpus artifact Q764287,
-- "Van der Waerden's theorem": every finite coloring of a commutative additive
-- monoid has a monochromatic positive-dilation-and-translation copy of each
-- finite subset. This file contains no proof.

{-# OPTIONS --safe #-}

module Q764287_van_der_waerden_s_theorem where

open import Agda.Primitive using (Level; Setω; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _and_

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Injective :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Set (a ⊔ b)
Injective {A = A} function =
  (x y : A) ->
  function x == function y ->
  x == y

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A -> B
    from    : B -> A
    from-to : (x : A) -> from (to x) == x
    to-from : (y : B) -> to (from y) == y

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size        : Nat
    equivalence : Bijection A (Fin size)

record FiniteSubset
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size      : Nat
    enumerate : Fin size -> A
    distinct  : Injective enumerate

open FiniteSubset

Member :
  {a : Level} ->
  {A : Set a} ->
  FiniteSubset A ->
  A ->
  Set a
Member subset item =
  Exists (Fin (size subset))
    (\ index -> item == enumerate subset index)

record AdditiveCommutativeMonoid
  {a : Level}
  (A : Set a) :
  Set a where

  field
    zeroA : A
    addA  : A -> A -> A

    add-associative :
      (x y z : A) ->
      addA (addA x y) z == addA x (addA y z)
    add-commutative :
      (x y : A) ->
      addA x y == addA y x
    add-zero-left :
      (x : A) ->
      addA zeroA x == x
    add-zero-right :
      (x : A) ->
      addA x zeroA == x

naturalScale :
  {a : Level} ->
  {A : Set a} ->
  AdditiveCommutativeMonoid A ->
  Nat ->
  A ->
  A
naturalScale monoid zero x =
  AdditiveCommutativeMonoid.zeroA monoid
naturalScale monoid (suc n) x =
  AdditiveCommutativeMonoid.addA monoid
    x
    (naturalScale monoid n x)

data Positive : Nat -> Set where
  positive-successor : {n : Nat} -> Positive (suc n)

van-der-waerden-s-theorem : Setω
van-der-waerden-s-theorem =
  {m k : Level} ->
  (M : Set m) ->
  (K : Set k) ->
  (monoid : AdditiveCommutativeMonoid M) ->
  (S : FiniteSubset M) ->
  Finite K ->
  (color : M -> K) ->
  Exists Nat
    (\ dilation ->
      Positive dilation
      and
      Exists M
        (\ translation ->
          Exists K
            (\ common-color ->
              (s : M) ->
              Member S s ->
              color
                (AdditiveCommutativeMonoid.addA monoid
                  (naturalScale monoid dilation s)
                  translation)
              ==
              common-color)))
