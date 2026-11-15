-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_a6:
-- the maximum number of sign patterns among nonzero solutions of two
-- homogeneous real linear equations in four variables is eight. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

five : Nat
five =
  suc four

six : Nat
six =
  suc five

seven : Nat
seven =
  suc six

eight : Nat
eight =
  suc seven

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
      fromNat (Agda.Builtin.Nat._+_ m n) ==
      add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (Agda.Builtin.Nat._*_ m n) ==
      multiply (fromNat m) (fromNat n)
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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

data Sign : Set where
  negative positive : Sign

HasSign :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Sign ->
  Set
HasSign reals x negative =
  StrictLess reals x (zeroR reals)
HasSign reals x positive =
  StrictLess reals (zeroR reals) x

Index : Set
Index =
  Fin four

Vector :
  Set ->
  Set
Vector R =
  Index -> R

SignPattern : Set
SignPattern =
  Index -> Sign

PatternEqual :
  SignPattern ->
  SignPattern ->
  Set
PatternEqual left-pattern right-pattern =
  (i : Index) ->
  left-pattern i == right-pattern i

index0 : Index
index0 =
  fzero

index1 : Index
index1 =
  fsuc fzero

index2 : Index
index2 =
  fsuc (fsuc fzero)

index3 : Index
index3 =
  fsuc (fsuc (fsuc fzero))

sumFour :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector R ->
  R
sumFour reals terms =
  add reals
    (terms index0)
    (add reals
      (terms index1)
      (add reals
        (terms index2)
        (terms index3)))

LinearCombination :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector R ->
  Vector R ->
  R
LinearCombination reals coefficients variables =
  sumFour reals
    (\ i ->
      multiply reals
        (coefficients i)
        (variables i))

NonzeroLeadingMinor :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector R ->
  Vector R ->
  Set
NonzeroLeadingMinor reals a b =
  subtract reals
    (multiply reals (a index0) (b index1))
    (multiply reals (a index1) (b index0))
  !=
  zeroR reals

PatternOccurs :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector R ->
  Vector R ->
  SignPattern ->
  Set
PatternOccurs {R} reals a b signs =
  Exists (Vector R)
    (\ x ->
      ((i : Index) -> x i != zeroR reals)
      and
      LinearCombination reals a x == zeroR reals
      and
      LinearCombination reals b x == zeroR reals
      and
      ((i : Index) -> HasSign reals (x i) (signs i)))

NumberOfPatterns :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector R ->
  Vector R ->
  Nat ->
  Set
NumberOfPatterns reals a b count =
  HasExtensionalCardinality
    PatternEqual
    (PatternOccurs reals a b)
    count

module Putnam1967A6Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  proposition : Set
  proposition =
    (numtuples : Vector R -> Vector R -> Nat) ->
    ((a b : Vector R) ->
      NumberOfPatterns reals a b (numtuples a b)) ->
    (Exists (Vector R)
      (\ a ->
        Exists (Vector R)
          (\ b ->
            NonzeroLeadingMinor reals a b
            and
            numtuples a b == eight)))
    and
    ((a b : Vector R) ->
      NonzeroLeadingMinor reals a b ->
      numtuples a b <=N eight)

putnam-1967-a6 : Set1
putnam-1967-a6 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1967A6Statement.proposition reals
