-- Statement-only formalization of Thousand Theorems corpus artifact Q619985,
-- "Multinomial theorem": the nth power of a finite sum in a semiring expands
-- over exponent vectors with multinomial coefficients when the summands
-- commute pairwise. This file contains no proof.

{-# OPTIONS --safe #-}

module Q619985_multinomial_theorem where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

data Bottom {a : Level} : Set a where

data Dec
  {p : Level}
  (P : Set p) :
  Set p where

  yes : P -> Dec P
  no  : (P -> Bottom {p}) -> Dec P

DecidableEquality :
  {a : Level} ->
  Set a ->
  Set a
DecidableEquality A =
  (x y : A) ->
  Dec (x == y)

_not-equal_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
_not-equal_ {a} x y =
  x == y -> Bottom {a}

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record FiniteSet
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size      : Nat
    enumerate : Fin size -> A
    distinct  :
      (i j : Fin size) ->
      enumerate i == enumerate j ->
      i == j

open FiniteSet

record Semiring
  {r : Level}
  (R : Set r) :
  Set r where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R

    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-zero-left :
      (x : R) ->
      addR zeroR x == x
    add-zero-right :
      (x : R) ->
      addR x zeroR == x

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-one-left :
      (x : R) ->
      multiplyR oneR x == x
    multiply-one-right :
      (x : R) ->
      multiplyR x oneR == x

    distribute-left :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) ->
      multiplyR (addR x y) z ==
      addR (multiplyR x z) (multiplyR y z)
    multiply-zero-left :
      (x : R) ->
      multiplyR zeroR x == zeroR
    multiply-zero-right :
      (x : R) ->
      multiplyR x zeroR == zeroR

Commute :
  {r : Level} ->
  {R : Set r} ->
  Semiring R ->
  R ->
  R ->
  Set r
Commute semiring x y =
  Semiring.multiplyR semiring x y ==
  Semiring.multiplyR semiring y x

PairwiseCommuting :
  {a r : Level} ->
  {A : Set a} ->
  {R : Set r} ->
  Semiring R ->
  (s : FiniteSet A) ->
  (A -> R) ->
  Set r
PairwiseCommuting semiring s f =
  (i j : Fin (size s)) ->
  i not-equal j ->
  Commute semiring
    (f (enumerate s i))
    (f (enumerate s j))

oneN : Nat
oneN =
  suc zero

choose : Nat -> Nat -> Nat
choose n zero =
  oneN
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n k + choose n (suc k)

natCast :
  {r : Level} ->
  {R : Set r} ->
  Semiring R ->
  Nat ->
  R
natCast semiring zero =
  Semiring.zeroR semiring
natCast semiring (suc n) =
  Semiring.addR semiring
    (natCast semiring n)
    (Semiring.oneR semiring)

power :
  {r : Level} ->
  {R : Set r} ->
  Semiring R ->
  R ->
  Nat ->
  R
power semiring x zero =
  Semiring.oneR semiring
power semiring x (suc n) =
  Semiring.multiplyR semiring
    (power semiring x n)
    x

sumFin :
  {r : Level} ->
  {R : Set r} ->
  (semiring : Semiring R) ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin semiring {zero} terms =
  Semiring.zeroR semiring
sumFin semiring {suc n} terms =
  Semiring.addR semiring
    (terms fzero)
    (sumFin semiring (\ i -> terms (fsuc i)))

productFin :
  {r : Level} ->
  {R : Set r} ->
  (semiring : Semiring R) ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
productFin semiring {zero} factors =
  Semiring.oneR semiring
productFin semiring {suc n} factors =
  Semiring.multiplyR semiring
    (factors fzero)
    (productFin semiring (\ i -> factors (fsuc i)))

sumNatFin :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumNatFin {zero} values =
  zero
sumNatFin {suc n} values =
  values fzero + sumNatFin (\ i -> values (fsuc i))

prepend :
  {n : Nat} ->
  Nat ->
  (Fin n -> Nat) ->
  Fin (suc n) ->
  Nat
prepend head tail fzero =
  head
prepend head tail (fsuc i) =
  tail i

emptyVector : Fin zero -> Nat
emptyVector ()

multinomial :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
multinomial {zero} powers =
  oneN
multinomial {suc n} powers =
  choose
    (powers fzero + sumNatFin (\ i -> powers (fsuc i)))
    (powers fzero)
  *
  multinomial (\ i -> powers (fsuc i))

sumThrough :
  {r : Level} ->
  {R : Set r} ->
  Semiring R ->
  Nat ->
  (Nat -> R) ->
  R
sumThrough semiring zero terms =
  terms zero
sumThrough semiring (suc n) terms =
  Semiring.addR semiring
    (sumThrough semiring n terms)
    (terms (suc n))

sumExponentVectors :
  {r : Level} ->
  {R : Set r} ->
  (semiring : Semiring R) ->
  (variables total : Nat) ->
  ((Fin variables -> Nat) -> R) ->
  R
sumExponentVectors semiring zero zero term =
  term emptyVector
sumExponentVectors semiring zero (suc total) term =
  Semiring.zeroR semiring
sumExponentVectors semiring (suc variables) total term =
  sumThrough semiring total
    (\ head ->
      sumExponentVectors semiring variables (total - head)
        (\ tail -> term (prepend head tail)))

multinomialTerm :
  {a r : Level} ->
  {A : Set a} ->
  {R : Set r} ->
  (semiring : Semiring R) ->
  (s : FiniteSet A) ->
  (f : A -> R) ->
  (Fin (size s) -> Nat) ->
  R
multinomialTerm semiring s f powers =
  Semiring.multiplyR semiring
    (natCast semiring (multinomial powers))
    (productFin semiring
      (\ i ->
        power semiring
          (f (enumerate s i))
          (powers i)))

-- Lean: Finset.sum_pow_eq_sum_piAntidiag_of_commute
multinomial-theorem : Setω
multinomial-theorem =
  {a r : Level} ->
  (A : Set a) ->
  (R : Set r) ->
  DecidableEquality A ->
  (semiring : Semiring R) ->
  (s : FiniteSet A) ->
  (f : A -> R) ->
  PairwiseCommuting semiring s f ->
  (n : Nat) ->
  power semiring
    (sumFin semiring (\ i -> f (enumerate s i)))
    n
  ==
  sumExponentVectors semiring (size s) n
    (multinomialTerm semiring s f)
