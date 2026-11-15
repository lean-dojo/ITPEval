-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_a5
-- (putnambench__agda__putnam_2013_a5): area definiteness of a real coefficient
-- array for all planar point configurations implies area definiteness for all
-- three-dimensional point configurations. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2013A5 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_

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

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc i) =
  suc (toNat i)

lessNat : Nat -> Nat -> Bool
lessNat zero zero =
  false
lessNat zero (suc n) =
  true
lessNat (suc m) zero =
  false
lessNat (suc m) (suc n) =
  lessNat m n

andBool : Bool -> Bool -> Bool
andBool true true =
  true
andBool _ _ =
  false

ifThenElse : {A : Set} -> Bool -> A -> A -> A
ifThenElse true when-true when-false =
  when-true
ifThenElse false when-true when-false =
  when-false

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR squareRootR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> addR x y == addR y x
    add-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    add-zero :
      (x : R) -> addR x zeroR == x
    add-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) -> multiplyR x oneR == x
    multiply-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zero :
      inverseR zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      (lessOrEqualR zeroR oneR) and (zeroR != oneR)

    fromNat-zero :
      fromNatR zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNat-injective :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

    square-root-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR (squareRootR x)
    square-root-square :
      (x : R) ->
      lessOrEqualR zeroR x ->
      multiplyR (squareRootR x) (squareRootR x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      squareRootR x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqualR zeroR y ->
      multiplyR y y == x ->
      y == squareRootR x

open CompleteOrderedRealField

two : Nat
two =
  suc (suc zero)

three : Nat
three =
  suc two

Vector : Set -> Nat -> Set
Vector R n =
  Fin n -> R

subtractR :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

squareR :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
squareR reals x =
  multiplyR reals x x

half :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
half reals =
  inverseR reals (addR reals (oneR reals) (oneR reals))

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  squareRootR reals (squareR reals x)

subtractVector :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
subtractVector reals u v i =
  subtractR reals (u i) (v i)

determinant2 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R two ->
  Vector R two ->
  R
determinant2 reals u v =
  subtractR reals
    (multiplyR reals
      (u fzero)
      (v (fsuc fzero)))
    (multiplyR reals
      (u (fsuc fzero))
      (v fzero))

triangleArea2 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R two ->
  Vector R two ->
  Vector R two ->
  R
triangleArea2 reals a b c =
  multiplyR reals
    (half reals)
    (absoluteValue reals
      (determinant2 reals
        (subtractVector reals b a)
        (subtractVector reals c a)))

cross3 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R three ->
  Vector R three ->
  Vector R three
cross3 reals u v fzero =
  subtractR reals
    (multiplyR reals (u (fsuc fzero)) (v (fsuc (fsuc fzero))))
    (multiplyR reals (u (fsuc (fsuc fzero))) (v (fsuc fzero)))
cross3 reals u v (fsuc fzero) =
  subtractR reals
    (multiplyR reals (u (fsuc (fsuc fzero))) (v fzero))
    (multiplyR reals (u fzero) (v (fsuc (fsuc fzero))))
cross3 reals u v (fsuc (fsuc fzero)) =
  subtractR reals
    (multiplyR reals (u fzero) (v (fsuc fzero)))
    (multiplyR reals (u (fsuc fzero)) (v fzero))

squaredNorm3 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R three ->
  R
squaredNorm3 reals v =
  addR reals
    (addR reals
      (squareR reals (v fzero))
      (squareR reals (v (fsuc fzero))))
    (squareR reals (v (fsuc (fsuc fzero))))

triangleArea3 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R three ->
  Vector R three ->
  Vector R three ->
  R
triangleArea3 reals a b c =
  multiplyR reals
    (half reals)
    (squareRootR reals
      (squaredNorm3 reals
        (cross3 reals
          (subtractVector reals b a)
          (subtractVector reals c a))))

sumFin :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedRealField R ->
  (Fin n -> R) ->
  R
sumFin {n = zero} reals term =
  zeroR reals
sumFin {n = suc n} reals term =
  addR reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

strictlyIncreasingTriple :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Fin n ->
  Bool
strictlyIncreasingTriple i j k =
  andBool
    (lessNat (toNat i) (toNat j))
    (lessNat (toNat j) (toNat k))

weightedAreaSum :
  {R : Set} ->
  {m dimension : Nat} ->
  CompleteOrderedRealField R ->
  (Vector R dimension -> Vector R dimension -> Vector R dimension -> R) ->
  (Fin m -> Fin m -> Fin m -> R) ->
  (Fin m -> Vector R dimension) ->
  R
weightedAreaSum reals area coefficients points =
  sumFin reals
    (\ i ->
      sumFin reals
        (\ j ->
          sumFin reals
            (\ k ->
              ifThenElse
                (strictlyIncreasingTriple i j k)
                (multiplyR reals
                  (coefficients i j k)
                  (area (points i) (points j) (points k)))
                (zeroR reals))))

AreaDefinite :
  {R : Set} ->
  {m dimension : Nat} ->
  (reals : CompleteOrderedRealField R) ->
  (Vector R dimension -> Vector R dimension -> Vector R dimension -> R) ->
  (Fin m -> Fin m -> Fin m -> R) ->
  Set
AreaDefinite {R} {m} {dimension} reals area coefficients =
  (points : Fin m -> Vector R dimension) ->
  lessOrEqualR reals
    (zeroR reals)
    (weightedAreaSum reals area coefficients points)

putnam-2013-a5 : Set1
putnam-2013-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (m : Nat) ->
  three <=N m ->
  (coefficients : Fin m -> Fin m -> Fin m -> R) ->
  AreaDefinite reals (triangleArea2 reals) coefficients ->
  AreaDefinite reals (triangleArea3 reals) coefficients
