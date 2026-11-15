-- Statement-only formalization of PutnamBench corpus artifact putnam_1992_b5
-- (putnambench__agda__putnam_1992_b5): the rational sequence obtained by
-- dividing the prescribed determinants by n factorial is unbounded. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam1992B5 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record RationalField (Q : Set) : Set1 where
  field
    zeroQ oneQ : Q
    add multiply : Q -> Q -> Q
    negate inverse : Q -> Q
    lessOrEqual : Q -> Q -> Set
    fromNat : Nat -> Q
    fromInt : Int -> Q

    one-not-zero :
      oneQ != zeroQ

    add-commutative :
      (x y : Q) -> add x y == add y x
    add-associative :
      (x y z : Q) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : Q) -> add x zeroQ == x
    add-inverse :
      (x : Q) -> add x (negate x) == zeroQ

    multiply-commutative :
      (x y : Q) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : Q) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : Q) -> multiply x oneQ == x
    multiply-zero :
      (x : Q) -> multiply x zeroQ == zeroQ
    distribute :
      (x y z : Q) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroQ == zeroQ
    multiply-inverse :
      (x : Q) ->
      x != zeroQ ->
      multiply x (inverse x) == oneQ

    order-reflexive :
      (x : Q) -> lessOrEqual x x
    order-transitive :
      (x y z : Q) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : Q) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : Q) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : Q) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : Q) ->
      lessOrEqual zeroQ x ->
      lessOrEqual zeroQ y ->
      lessOrEqual zeroQ (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroQ oneQ and zeroQ != oneQ

    fromNat-zero :
      fromNat zero == zeroQ
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneQ
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

    fromInt-nonnegative :
      (n : Nat) ->
      fromInt (pos n) == fromNat n
    fromInt-negative :
      (n : Nat) ->
      fromInt (negsuc n) == negate (fromNat (suc n))

    every-element-is-ratio :
      (x : Q) ->
      Exists Int
        (\ numerator ->
          Exists Nat
            (\ denominator-minus-one ->
              x ==
              multiply
                (fromInt numerator)
                (inverse
                  (fromNat (suc denominator-minus-one)))))

open RationalField

divide :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Q ->
  Q
divide rationals x y =
  multiply rationals x (inverse rationals y)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc i) =
  suc (toNat i)

sameFin : {n : Nat} -> Fin n -> Fin n -> Bool
sameFin fzero fzero =
  true
sameFin fzero (fsuc j) =
  false
sameFin (fsuc i) fzero =
  false
sameFin (fsuc i) (fsuc j) =
  sameFin i j

ifBool : {A : Set} -> Bool -> A -> A -> A
ifBool true whenTrue whenFalse =
  whenTrue
ifBool false whenTrue whenFalse =
  whenFalse

predecessor : Nat -> Nat
predecessor zero =
  zero
predecessor (suc n) =
  n

Matrix : Set -> Nat -> Nat -> Set
Matrix Q rows columns =
  Fin rows -> Fin columns -> Q

sumFin :
  {Q : Set} ->
  RationalField Q ->
  {n : Nat} ->
  (Fin n -> Q) ->
  Q
sumFin rationals {zero} term =
  zeroQ rationals
sumFin rationals {suc n} term =
  add rationals
    (term fzero)
    (sumFin rationals (\ i -> term (fsuc i)))

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
  {Q : Set} {n : Nat} ->
  Matrix Q (suc n) (suc n) ->
  Fin (suc n) ->
  Matrix Q n n
firstRowMinor A removedColumn i j =
  A (fsuc i) (skip removedColumn j)

alternatingSign :
  {Q : Set} ->
  RationalField Q ->
  {n : Nat} ->
  Fin n ->
  Q
alternatingSign rationals fzero =
  oneQ rationals
alternatingSign rationals (fsuc i) =
  negate rationals (alternatingSign rationals i)

determinant :
  {Q : Set} ->
  RationalField Q ->
  {n : Nat} ->
  Matrix Q n n ->
  Q
determinant rationals {zero} A =
  oneQ rationals
determinant rationals {suc n} A =
  sumFin rationals
    (\ column ->
      multiply rationals
        (alternatingSign rationals column)
        (multiply rationals
          (A fzero column)
          (determinant rationals (firstRowMinor A column))))

three : Nat
three =
  suc (suc (suc zero))

two : Nat
two =
  suc (suc zero)

prescribedMatrix :
  {Q : Set} ->
  RationalField Q ->
  (n : Nat) ->
  Matrix Q (predecessor n) (predecessor n)
prescribedMatrix rationals n i j =
  ifBool
    (sameFin i j)
    (fromNat rationals (toNat i + three))
    (oneQ rationals)

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

NormalizedDeterminant :
  {Q : Set} ->
  RationalField Q ->
  (Nat -> Q) ->
  Nat ->
  Q
NormalizedDeterminant rationals D n =
  divide rationals
    (D n)
    (fromNat rationals (factorial n))

AbsoluteValueAtMost :
  {Q : Set} ->
  RationalField Q ->
  Q ->
  Q ->
  Set
AbsoluteValueAtMost rationals x bound =
  lessOrEqual rationals (negate rationals x) bound
  and
  lessOrEqual rationals x bound

BoundedNormalizedDeterminants :
  {Q : Set} ->
  RationalField Q ->
  (Nat -> Q) ->
  Set
BoundedNormalizedDeterminants rationals D =
  Exists _
    (\ bound ->
      (n : Nat) ->
      two <=N n ->
      AbsoluteValueAtMost rationals
        (NormalizedDeterminant rationals D n)
        bound)

putnam-1992-b5-solution : Set
putnam-1992-b5-solution =
  Bottom

putnam-1992-b5 : Set1
putnam-1992-b5 =
  (Q : Set) ->
  (rationals : RationalField Q) ->
  (D : Nat -> Q) ->
  ((n : Nat) ->
    D n ==
    determinant rationals (prescribedMatrix rationals n)) ->
  Iff
    (BoundedNormalizedDeterminants rationals D)
    putnam-1992-b5-solution
