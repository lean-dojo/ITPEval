-- Statement-only formalization of PutnamBench corpus artifact putnam_2003_a5
-- (putnambench__agda__putnam_2003_a5): Dyck n-paths with no even-length
-- return are in one-to-one correspondence with Dyck (n-1)-paths. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2003A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<F_ _<=F_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive :
    {n : Nat} ->
    Positive (suc n)

data Fin : Nat -> Set where
  fzero :
    {n : Nat} ->
    Fin (suc n)
  fsuc :
    {n : Nat} ->
    Fin n ->
    Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

data _<F_ : {n : Nat} -> Fin n -> Fin n -> Set where
  fzero<fsuc :
    {n : Nat} {j : Fin n} ->
    fzero <F fsuc j
  fsuc<fsuc :
    {n : Nat} {i j : Fin n} ->
    i <F j ->
    fsuc i <F fsuc j

data _<=F_ : {n : Nat} -> Fin n -> Fin n -> Set where
  fzero<= :
    {n : Nat} {j : Fin (suc n)} ->
    fzero <=F j
  fsuc<=fsuc :
    {n : Nat} {i j : Fin n} ->
    i <=F j ->
    fsuc i <=F fsuc j

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

zeroZ : Int
zeroZ =
  pos zero

oneZ : Int
oneZ =
  pos (suc zero)

minusOneZ : Int
minusOneZ =
  negsuc zero

two : Nat
two =
  suc (suc zero)

data Step : Int -> Set where
  up-step :
    Step oneZ
  down-step :
    Step minusOneZ

data Nonnegative : Int -> Set where
  nonnegative :
    {n : Nat} ->
    Nonnegative (pos n)

data Even : Nat -> Set where
  even-zero :
    Even zero
  even-plus-two :
    {n : Nat} ->
    Even n ->
    Even (suc (suc n))

Path : Nat -> Set
Path m =
  Fin (two * m) -> Int

sumFin :
  {n : Nat} ->
  (Fin n -> Int) ->
  Int
sumFin {zero} terms =
  zeroZ
sumFin {suc n} terms =
  addInt
    (terms fzero)
    (sumFin (\ i -> terms (fsuc i)))

prefixSum :
  {n : Nat} ->
  (Fin n -> Int) ->
  Fin n ->
  Int
prefixSum {suc n} path fzero =
  path fzero
prefixSum {suc n} path (fsuc j) =
  addInt
    (path fzero)
    (prefixSum (\ i -> path (fsuc i)) j)

PathEqual :
  {m : Nat} ->
  Path m ->
  Path m ->
  Set
PathEqual {m} left right =
  (i : Fin (two * m)) ->
  left i == right i

record IsDyckPath (m : Nat) (path : Path m) : Set where
  field
    unit-steps :
      (i : Fin (two * m)) ->
      Step (path i)
    balanced :
      sumFin path == zeroZ
    nonnegative-prefixes :
      (j : Fin (two * m)) ->
      Nonnegative (prefixSum path j)

record HasEvenReturn (m : Nat) (path : Path m) : Set where
  field
    preceding-index :
      Fin (two * m)
    return-index :
      Fin (two * m)
    precedes-return :
      preceding-index <F return-index
    preceding-up-step :
      path preceding-index == oneZ
    contiguous-down-steps :
      (k : Fin (two * m)) ->
      preceding-index <F k ->
      k <=F return-index ->
      path k == minusOneZ
    even-return-length :
      Even
        (finToNat return-index - finToNat preceding-index)
    returns-to-axis :
      prefixSum path return-index == zeroZ

NoEvenReturn :
  (m : Nat) ->
  Path m ->
  Set
NoEvenReturn m path =
  Not (HasEvenReturn m path)

record IsSpecialDyckPath (m : Nat) (path : Path m) : Set where
  field
    is-dyck-path :
      IsDyckPath m path
    has-no-even-return :
      NoEvenReturn m path

record DyckPathBijection (n : Nat) : Set where
  field
    forward :
      Path n ->
      Path (n - suc zero)
    backward :
      Path (n - suc zero) ->
      Path n
    forward-preserves-membership :
      (path : Path n) ->
      IsSpecialDyckPath n path ->
      IsDyckPath (n - suc zero) (forward path)
    backward-preserves-membership :
      (path : Path (n - suc zero)) ->
      IsDyckPath (n - suc zero) path ->
      IsSpecialDyckPath n (backward path)
    backward-after-forward :
      (path : Path n) ->
      IsSpecialDyckPath n path ->
      PathEqual {m = n} (backward (forward path)) path
    forward-after-backward :
      (path : Path (n - suc zero)) ->
      IsDyckPath (n - suc zero) path ->
      PathEqual {m = n - suc zero} (forward (backward path)) path

putnam-2003-a5 : Set
putnam-2003-a5 =
  (n : Nat) ->
  Positive n ->
  DyckPathBijection n
