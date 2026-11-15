-- Statement-only formalization of thousand-theorems corpus artifact
-- thousand-theorems__agda__Q716171, "Erdős–Ginzburg–Ziv theorem": any finite
-- set of at least 2 * n - 1 indices labeled in Z/nZ contains an n-element
-- subset whose labels sum to zero. This file contains no proof.

{-# OPTIONS --safe #-}

module Q716171_erd_s_ginzburg_ziv_theorem where

open import Agda.Primitive using (Level; _⊔_; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=_
infixr 3 _and_
infixl 6 _+z_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

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

data LastView (n : Nat) : Set where
  before-last : Fin n -> LastView n
  at-last     : LastView n

viewLast :
  {n : Nat} ->
  Fin (suc n) ->
  LastView n
viewLast {zero} fzero =
  at-last
viewLast {suc n} fzero =
  before-last fzero
viewLast {suc n} (fsuc i) with viewLast i
... | before-last j =
  before-last (fsuc j)
... | at-last =
  at-last

successorMod :
  {n : Nat} ->
  Fin (suc n) ->
  Fin (suc n)
successorMod x with viewLast x
... | before-last j =
  fsuc j
... | at-last =
  fzero

finToNat :
  {n : Nat} ->
  Fin n ->
  Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

iterateSuccessor :
  {n : Nat} ->
  Nat ->
  Fin (suc n) ->
  Fin (suc n)
iterateSuccessor zero x =
  x
iterateSuccessor (suc count) x =
  iterateSuccessor count (successorMod x)

addFin :
  {n : Nat} ->
  Fin (suc n) ->
  Fin (suc n) ->
  Fin (suc n)
addFin x y =
  iterateSuccessor (finToNat y) x

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

_+z_ : Int -> Int -> Int
pos m +z pos n =
  pos (m + n)
pos m +z negsuc n =
  difference m (suc n)
negsuc m +z pos n =
  difference n (suc m)
negsuc m +z negsuc n =
  negsuc (suc (m + n))

data ZMod : Nat -> Set where
  integer-residue :
    Int ->
    ZMod zero
  finite-residue :
    {n : Nat} ->
    Fin (suc n) ->
    ZMod (suc n)

zeroZMod :
  (n : Nat) ->
  ZMod n
zeroZMod zero =
  integer-residue (pos zero)
zeroZMod (suc n) =
  finite-residue fzero

addZMod :
  {n : Nat} ->
  ZMod n ->
  ZMod n ->
  ZMod n
addZMod {zero} (integer-residue x) (integer-residue y) =
  integer-residue (x +z y)
addZMod {suc n} (finite-residue x) (finite-residue y) =
  finite-residue (addFin x y)

record FiniteSubset
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

SubsetOf :
  {a : Level} ->
  {A : Set a} ->
  FiniteSubset A ->
  FiniteSubset A ->
  Set a
SubsetOf child parent =
  (index : Fin (size child)) ->
  Member parent (enumerate child index)

sumFin :
  {n count : Nat} ->
  (Fin count -> ZMod n) ->
  ZMod n
sumFin {n} {zero} values =
  zeroZMod n
sumFin {n} {suc count} values =
  addZMod
    (values fzero)
    (sumFin (\ index -> values (fsuc index)))

sumFiniteSubset :
  {a : Level} ->
  {A : Set a} ->
  {n : Nat} ->
  (A -> ZMod n) ->
  FiniteSubset A ->
  ZMod n
sumFiniteSubset values subset =
  sumFin (\ index -> values (enumerate subset index))

-- Lean: ZMod.erdos_ginzburg_ziv
erdos-ginzburg-ziv-theorem : Setω
erdos-ginzburg-ziv-theorem =
  {a : Level} ->
  (I : Set a) ->
  (n : Nat) ->
  (s : FiniteSubset I) ->
  (values : I -> ZMod n) ->
  2 * n - 1 <= size s ->
  Exists (FiniteSubset I)
    (\ t ->
      SubsetOf t s
      and
      ((size t == n)
       and
       (sumFiniteSubset values t == zeroZMod n)))
