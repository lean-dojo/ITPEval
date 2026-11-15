-- Statement-only formalization of PutnamBench corpus artifact putnam_2022_b5
-- (putnambench__agda__putnam_2022_b5): the parameters for which zero is a
-- most likely weighted sum of independent ternary random variables. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 5 _++_
infixr 3 _and_
infixr 2 _or_
infixl 6 _+Z_
infixl 7 _*Z_

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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

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

twoN : Nat
twoN =
  suc (suc zero)

fourN : Nat
fourN =
  suc (suc twoN)

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negative (m * suc n)
negsuc m *Z pos n =
  negative (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

zeroZ : Int
zeroZ =
  pos zero

oneZ : Int
oneZ =
  pos (suc zero)

negativeOneZ : Int
negativeOneZ =
  negsuc zero

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

intEqual : Int -> Int -> Bool
intEqual (pos m) (pos n) =
  natEqual m n
intEqual (pos m) (negsuc n) =
  false
intEqual (negsuc m) (pos n) =
  false
intEqual (negsuc m) (negsuc n) =
  natEqual m n

data Vector (A : Set) : Nat -> Set where
  []V  : Vector A zero
  _∷V_ : {n : Nat} -> A -> Vector A n -> Vector A (suc n)

infixr 5 _∷V_

IsTernary : Int -> Set
IsTernary x =
  (x == oneZ) or ((x == negativeOneZ) or (x == zeroZ))

data AllTernary : {n : Nat} -> Vector Int n -> Set where
  all-empty :
    AllTernary []V
  all-cons :
    {n : Nat} ->
    {x : Int} ->
    {xs : Vector Int n} ->
    IsTernary x ->
    AllTernary xs ->
    AllTernary (x ∷V xs)

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys =
  ys
(x ∷ xs) ++ ys =
  x ∷ (xs ++ ys)

prependAll :
  {A : Set} ->
  {n : Nat} ->
  A ->
  List (Vector A n) ->
  List (Vector A (suc n))
prependAll x [] =
  []
prependAll x (xs ∷ xss) =
  (x ∷V xs) ∷ prependAll x xss

allTernaryVectors :
  (n : Nat) ->
  List (Vector Int n)
allTernaryVectors zero =
  []V ∷ []
allTernaryVectors (suc n) =
  prependAll negativeOneZ (allTernaryVectors n) ++
  prependAll zeroZ (allTernaryVectors n) ++
  prependAll oneZ (allTernaryVectors n)

dotProduct :
  {n : Nat} ->
  Vector Int n ->
  Vector Int n ->
  Int
dotProduct []V []V =
  zeroZ
dotProduct (a ∷V as) (x ∷V xs) =
  (a *Z x) +Z dotProduct as xs

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

probabilityFactor :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Int ->
  R
probabilityFactor reals p (pos zero) =
  subtract reals
    (oneR reals)
    (multiply reals (fromNat reals twoN) p)
probabilityFactor reals p (pos (suc zero)) =
  p
probabilityFactor reals p (pos (suc (suc n))) =
  subtract reals
    (oneR reals)
    (multiply reals (fromNat reals twoN) p)
probabilityFactor reals p (negsuc zero) =
  p
probabilityFactor reals p (negsuc (suc n)) =
  subtract reals
    (oneR reals)
    (multiply reals (fromNat reals twoN) p)

productProbability :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  {n : Nat} ->
  Vector Int n ->
  R
productProbability reals p []V =
  oneR reals
productProbability reals p (x ∷V xs) =
  multiply reals
    (probabilityFactor reals p x)
    (productProbability reals p xs)

sumMatching :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Vector Int n -> R) ->
  Vector Int n ->
  Int ->
  List (Vector Int n) ->
  R
sumMatching reals probability coefficients target [] =
  zeroR reals
sumMatching reals probability coefficients target (x ∷ xs)
  with intEqual (dotProduct coefficients x) target
... | true =
  add reals
    (probability x)
    (sumMatching reals probability coefficients target xs)
... | false =
  sumMatching reals probability coefficients target xs

oneHalf :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
oneHalf reals =
  divide reals
    (oneR reals)
    (fromNat reals twoN)

oneQuarter :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
oneQuarter reals =
  divide reals
    (oneR reals)
    (fromNat reals fourN)

putnam-2022-b5 : Set1
putnam-2022-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (p : R) ->
  (Xset : (n : Nat) -> Vector Int n -> Set) ->
  (Xprob : (n : Nat) -> Vector Int n -> R) ->
  (P : (n : Nat) -> Int -> Vector Int n -> R) ->
  ((n : Nat) ->
    Positive n ->
    (X : Vector Int n) ->
    Iff (Xset n X) (AllTernary X)) ->
  ((n : Nat) ->
    Positive n ->
    (X : Vector Int n) ->
    Xprob n X == productProbability reals p X) ->
  ((n : Nat) ->
    Positive n ->
    (b : Int) ->
    (a : Vector Int n) ->
    P n b a ==
      sumMatching reals
        (Xprob n)
        a
        b
        (allTernaryVectors n)) ->
  Iff
    (lessOrEqual reals (zeroR reals) p
    and
    (lessOrEqual reals p (oneHalf reals)
    and
    ((n : Nat) ->
      Positive n ->
      (b : Int) ->
      (a : Vector Int n) ->
      lessOrEqual reals (P n b a) (P n zeroZ a))))
    (lessOrEqual reals (zeroR reals) p
    and
    lessOrEqual reals p (oneQuarter reals))
