-- Statement-only formalization of Thousand Theorems corpus artifact Q720469,
-- "Chevalley–Warning theorem": over a finite field of characteristic p, the
-- characteristic divides the number of common zeros of a finite polynomial
-- family when the sum of total degrees is smaller than the number of variables.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q720469_chevalley_warning_theorem where

open import Agda.Primitive using (Level; Setω; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ _not-equal_ _divides_
infixr 3 _and_
infix 2 _iff_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

_not-equal_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x not-equal y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    first  : A
    second : B

record _iff_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    forward  : A -> B
    backward : B -> A

data Dec
  {a : Level}
  (A : Set a) :
  Set a where

  yes : A -> Dec A
  no  : Not A -> Dec A

DecidableEquality :
  {a : Level} ->
  Set a ->
  Set a
DecidableEquality A =
  (x y : A) ->
  Dec (x == y)

data _<_ : Nat -> Nat -> Set where
  zero-less-suc :
    {n : Nat} ->
    zero < suc n
  suc-less-suc :
    {m n : Nat} ->
    m < n ->
    suc m < suc n

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient == dividend

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data Vector
  {a : Level}
  (A : Set a) :
  Nat ->
  Set a where

  vector-empty :
    Vector A zero
  vector-cons :
    {n : Nat} ->
    A ->
    Vector A n ->
    Vector A (suc n)

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

record FiniteType
  {a : Level}
  (A : Set a) :
  Set a where

  field
    cardinality : Nat
    enumeration : Bijection (Fin cardinality) A

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A ->
  Set a where

  here :
    {xs : List A} ->
    Member x (x ∷ xs)
  there :
    {y : A} {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

data NoDuplicates
  {a : Level}
  {A : Set a} :
  List A ->
  Set a where

  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} ->
    Not (Member x xs) ->
    NoDuplicates xs ->
    NoDuplicates (x ∷ xs)

record FiniteSubset
  {a : Level}
  (A : Set a) :
  Set a where

  field
    elements      : List A
    no-duplicates : NoDuplicates elements

record Field
  {a : Level}
  (K : Set a) :
  Set a where

  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK inverseK : K -> K

    one-not-zero :
      oneK not-equal zeroK

    add-associative :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-commutative :
      (x y : K) ->
      addK x y == addK y x
    add-zero :
      (x : K) ->
      addK x zeroK == x
    add-inverse :
      (x : K) ->
      addK x (negateK x) == zeroK

    multiply-associative :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ==
      multiplyK x (multiplyK y z)
    multiply-commutative :
      (x y : K) ->
      multiplyK x y == multiplyK y x
    multiply-one :
      (x : K) ->
      multiplyK x oneK == x
    distribute :
      (x y z : K) ->
      multiplyK x (addK y z) ==
      addK (multiplyK x y) (multiplyK x z)
    multiply-inverse :
      (x : K) ->
      x not-equal zeroK ->
      multiplyK x (inverseK x) == oneK
    inverse-zero :
      inverseK zeroK == zeroK

fromNat :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  Nat ->
  K
fromNat algebra zero =
  Field.zeroK algebra
fromNat algebra (suc n) =
  Field.addK algebra
    (fromNat algebra n)
    (Field.oneK algebra)

record Characteristic
  {a : Level}
  {K : Set a}
  (algebra : Field K)
  (p : Nat) :
  Set a where

  field
    cast-is-zero :
      (n : Nat) ->
      (fromNat algebra n == Field.zeroK algebra)
      iff
      (p divides n)

power :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  Nat ->
  K
power algebra x zero =
  Field.oneK algebra
power algebra x (suc n) =
  Field.multiplyK algebra x (power algebra x n)

maxNat :
  Nat ->
  Nat ->
  Nat
maxNat zero n =
  n
maxNat (suc m) zero =
  suc m
maxNat (suc m) (suc n) =
  suc (maxNat m n)

Exponent :
  {s : Level} ->
  {Sigma : Set s} ->
  FiniteType Sigma ->
  Set
Exponent finiteSigma =
  Vector Nat (FiniteType.cardinality finiteSigma)

sumVector :
  {n : Nat} ->
  Vector Nat n ->
  Nat
sumVector vector-empty =
  zero
sumVector (vector-cons value values) =
  value + sumVector values

monomialDegree :
  {s : Level} ->
  {Sigma : Set s} ->
  (finiteSigma : FiniteType Sigma) ->
  Exponent finiteSigma ->
  Nat
monomialDegree finiteSigma exponent =
  sumVector exponent

record Polynomial
  {k s : Level}
  {K : Set k}
  {Sigma : Set s}
  (algebra : Field K)
  (finiteSigma : FiniteType Sigma) :
  Set (k ⊔ s) where

  field
    coefficient :
      Exponent finiteSigma ->
      K
    support :
      List (Exponent finiteSigma)
    support-exact :
      (exponent : Exponent finiteSigma) ->
      Member exponent support
      iff
      (coefficient exponent not-equal Field.zeroK algebra)
    support-no-duplicates :
      NoDuplicates support

maximumDegree :
  {s : Level} ->
  {Sigma : Set s} ->
  (finiteSigma : FiniteType Sigma) ->
  List (Exponent finiteSigma) ->
  Nat
maximumDegree finiteSigma [] =
  zero
maximumDegree finiteSigma (exponent ∷ support) =
  maxNat
    (monomialDegree finiteSigma exponent)
    (maximumDegree finiteSigma support)

totalDegree :
  {k s : Level}
  {K : Set k}
  {Sigma : Set s}
  {algebra : Field K}
  {finiteSigma : FiniteType Sigma} ->
  Polynomial algebra finiteSigma ->
  Nat
totalDegree {finiteSigma = finiteSigma} polynomial =
  maximumDegree finiteSigma (Polynomial.support polynomial)

monomialProduct :
  {k : Level}
  {K : Set k} ->
  (algebra : Field K) ->
  {n : Nat} ->
  (Fin n -> K) ->
  Vector Nat n ->
  K
monomialProduct algebra values vector-empty =
  Field.oneK algebra
monomialProduct algebra values (vector-cons exponent exponents) =
  Field.multiplyK algebra
    (power algebra (values fzero) exponent)
    (monomialProduct algebra
      (\ i -> values (fsuc i))
      exponents)

monomialValue :
  {k s : Level}
  {K : Set k}
  {Sigma : Set s} ->
  (algebra : Field K) ->
  (finiteSigma : FiniteType Sigma) ->
  (Sigma -> K) ->
  Exponent finiteSigma ->
  K
monomialValue algebra finiteSigma assignment exponent =
  monomialProduct algebra
    (\ i ->
      assignment
        (Bijection.to
          (FiniteType.enumeration finiteSigma)
          i))
    exponent

evaluateSupport :
  {k s : Level}
  {K : Set k}
  {Sigma : Set s} ->
  (algebra : Field K) ->
  (finiteSigma : FiniteType Sigma) ->
  (coefficient : Exponent finiteSigma -> K) ->
  List (Exponent finiteSigma) ->
  (Sigma -> K) ->
  K
evaluateSupport algebra finiteSigma coefficient [] assignment =
  Field.zeroK algebra
evaluateSupport algebra finiteSigma coefficient
  (exponent ∷ support) assignment =
  Field.addK algebra
    (Field.multiplyK algebra
      (coefficient exponent)
      (monomialValue algebra finiteSigma assignment exponent))
    (evaluateSupport algebra finiteSigma coefficient support assignment)

evaluate :
  {k s : Level}
  {K : Set k}
  {Sigma : Set s} ->
  (algebra : Field K) ->
  (finiteSigma : FiniteType Sigma) ->
  Polynomial algebra finiteSigma ->
  (Sigma -> K) ->
  K
evaluate algebra finiteSigma polynomial assignment =
  evaluateSupport algebra finiteSigma
    (Polynomial.coefficient polynomial)
    (Polynomial.support polynomial)
    assignment

sumDegrees :
  {i k s : Level}
  {I : Set i}
  {K : Set k}
  {Sigma : Set s}
  {algebra : Field K}
  {finiteSigma : FiniteType Sigma} ->
  List I ->
  (I -> Polynomial algebra finiteSigma) ->
  Nat
sumDegrees [] family =
  zero
sumDegrees (index ∷ indices) family =
  totalDegree (family index) + sumDegrees indices family

CommonZero :
  {i k s : Level}
  {I : Set i}
  {K : Set k}
  {Sigma : Set s} ->
  (algebra : Field K) ->
  (finiteSigma : FiniteType Sigma) ->
  FiniteSubset I ->
  (I -> Polynomial algebra finiteSigma) ->
  (Sigma -> K) ->
  Set (i ⊔ k)
CommonZero algebra finiteSigma subset family assignment =
  (index : _) ->
  Member index (FiniteSubset.elements subset) ->
  evaluate algebra finiteSigma (family index) assignment ==
  Field.zeroK algebra

AssignmentEqual :
  {k s : Level}
  {K : Set k}
  {Sigma : Set s} ->
  FiniteType Sigma ->
  (Sigma -> K) ->
  (Sigma -> K) ->
  Set k
AssignmentEqual finiteSigma left right =
  (index : Fin (FiniteType.cardinality finiteSigma)) ->
  left
    (Bijection.to
      (FiniteType.enumeration finiteSigma)
      index)
  ==
  right
    (Bijection.to
      (FiniteType.enumeration finiteSigma)
      index)

record HasCardinality
  {a p e : Level}
  {A : Set a}
  (member : A -> Set p)
  (equivalent : A -> A -> Set e)
  (cardinality : Nat) :
  Set (a ⊔ p ⊔ e) where

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
      Σ (Fin cardinality)
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

chevalley-warning-theorem : Setω
chevalley-warning-theorem =
  {k s i : Level} ->
  (K : Set k) ->
  (Sigma : Set s) ->
  (I : Set i) ->
  (algebra : Field K) ->
  FiniteType K ->
  DecidableEquality K ->
  (finiteSigma : FiniteType Sigma) ->
  DecidableEquality Sigma ->
  (p : Nat) ->
  Characteristic algebra p ->
  (subset : FiniteSubset I) ->
  (family : I -> Polynomial algebra finiteSigma) ->
  sumDegrees (FiniteSubset.elements subset) family
    < FiniteType.cardinality finiteSigma ->
  Σ Nat
    (\ solution-count ->
      HasCardinality
        (CommonZero algebra finiteSigma subset family)
        (AssignmentEqual finiteSigma)
        solution-count
      and
      (p divides solution-count))
