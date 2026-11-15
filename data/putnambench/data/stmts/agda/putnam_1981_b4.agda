-- Statement-only formalization of PutnamBench corpus artifact putnam_1981_b4:
-- the assertion that a real linear subspace of 5 by 7 matrices containing
-- ranks 0, 1, 2, 4, and 5 must also contain rank 3 is false.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value     : A
    satisfies : property value

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
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
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
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

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
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Matrix : Set -> Nat -> Nat -> Set
Matrix R rows columns =
  Fin rows -> Fin columns -> R

Predicate : Set -> Set1
Predicate A =
  A -> Set

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc n} term =
  add reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

skip :
  {n : Nat} ->
  Fin (suc n) ->
  Fin n ->
  Fin (suc n)
skip {zero} removed ()
skip {suc n} fzero i =
  fsuc i
skip {suc n} (fsuc removed) fzero =
  fzero
skip {suc n} (fsuc removed) (fsuc i) =
  fsuc (skip removed i)

firstRowMinor :
  {R : Set} {n : Nat} ->
  Matrix R (suc n) (suc n) ->
  Fin (suc n) ->
  Matrix R n n
firstRowMinor A removedColumn i j =
  A (fsuc i) (skip removedColumn j)

alternatingSign :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Fin n ->
  R
alternatingSign reals fzero =
  oneR reals
alternatingSign reals (fsuc i) =
  negate reals (alternatingSign reals i)

determinant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n n ->
  R
determinant reals {zero} A =
  oneR reals
determinant reals {suc n} A =
  sumFin reals
    (\ column ->
      multiply reals
        (alternatingSign reals column)
        (multiply reals
          (A fzero column)
          (determinant reals (firstRowMinor A column))))

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective f =
  (x y : _) ->
  f x == f y ->
  x == y

submatrix :
  {R : Set} {rows columns k : Nat} ->
  Matrix R rows columns ->
  (Fin k -> Fin rows) ->
  (Fin k -> Fin columns) ->
  Matrix R k k
submatrix A selectedRows selectedColumns i j =
  A (selectedRows i) (selectedColumns j)

RankAtLeast :
  {R : Set} {rows columns : Nat} ->
  CompleteOrderedRealField R ->
  Matrix R rows columns ->
  Nat ->
  Set
RankAtLeast {rows = rows} {columns = columns} reals A k =
  Exists (Fin k -> Fin rows)
    (\ selectedRows ->
      Injective selectedRows
      and
      Exists (Fin k -> Fin columns)
        (\ selectedColumns ->
          Injective selectedColumns
          and
          determinant reals
            (submatrix A selectedRows selectedColumns)
          !=
          zeroR reals))

HasRank :
  {R : Set} {rows columns : Nat} ->
  CompleteOrderedRealField R ->
  Matrix R rows columns ->
  Nat ->
  Set
HasRank reals A k =
  RankAtLeast reals A k
  and
  Not (RankAtLeast reals A (suc k))

zeroN : Nat
zeroN =
  zero

oneN : Nat
oneN =
  suc zeroN

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  suc threeN

fiveN : Nat
fiveN =
  suc fourN

sixN : Nat
sixN =
  suc fiveN

sevenN : Nat
sevenN =
  suc sixN

linearCombination :
  {R : Set} {rows columns : Nat} ->
  CompleteOrderedRealField R ->
  R ->
  Matrix R rows columns ->
  R ->
  Matrix R rows columns ->
  Matrix R rows columns
linearCombination reals r A s B i j =
  add reals
    (multiply reals r (A i j))
    (multiply reals s (B i j))

ClosedUnderLinearCombinations :
  {R : Set} {rows columns : Nat} ->
  CompleteOrderedRealField R ->
  Predicate (Matrix R rows columns) ->
  Set
ClosedUnderLinearCombinations reals V =
  (A B : _) ->
  V A ->
  V B ->
  (r s : _) ->
  V (linearCombination reals r A s B)

ContainsRank :
  {R : Set} {rows columns : Nat} ->
  CompleteOrderedRealField R ->
  Predicate (Matrix R rows columns) ->
  Nat ->
  Set
ContainsRank reals V k =
  Exists _
    (\ A ->
      V A
      and
      HasRank reals A k)

Assertion :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Set1
Assertion {R} reals =
  (V : Predicate (Matrix R fiveN sevenN)) ->
  ClosedUnderLinearCombinations reals V ->
  ContainsRank reals V zeroN ->
  ContainsRank reals V oneN ->
  ContainsRank reals V twoN ->
  ContainsRank reals V fourN ->
  ContainsRank reals V fiveN ->
  ContainsRank reals V threeN

putnam-1981-b4-solution : Set
putnam-1981-b4-solution =
  Bottom

putnam-1981-b4 : Set1
putnam-1981-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Iff
    (Assertion reals)
    putnam-1981-b4-solution
