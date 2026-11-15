-- Statement-only formalization of Thousand Theorems corpus artifact Q7433182,
-- "Schwartz–Zippel theorem": the fraction of zeros of a nonzero multivariate
-- polynomial on a product of finite subsets is bounded by the maximum, over
-- supported monomials, of the sum of coordinate degrees divided by subset
-- cardinalities. This file contains no proof.

{-# OPTIONS --safe #-}

module Q7433182_schwartz_zippel_theorem where

open import Agda.Primitive using (Level; Setω; _⊔_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _not-equal_ _less-or-equal_
infixr 3 _or_
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

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

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

data _less-or-equal_ : Nat -> Nat -> Set where
  zero-less-or-equal :
    {n : Nat} ->
    zero less-or-equal n
  suc-less-or-equal :
    {m n : Nat} ->
    m less-or-equal n ->
    suc m less-or-equal suc n

lessOrEqualBool :
  Nat ->
  Nat ->
  Bool
lessOrEqualBool zero n =
  true
lessOrEqualBool (suc m) zero =
  false
lessOrEqualBool (suc m) (suc n) =
  lessOrEqualBool m n

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

length :
  {a : Level} ->
  {A : Set a} ->
  List A ->
  Nat
length [] =
  zero
length (x ∷ xs) =
  suc (length xs)

cardinality :
  {a : Level} ->
  {A : Set a} ->
  FiniteSubset A ->
  Nat
cardinality subset =
  length (FiniteSubset.elements subset)

record IntegralDomain
  {a : Level}
  (R : Set a) :
  Set a where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR : R -> R

    one-not-zero :
      oneR not-equal zeroR

    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-zero :
      (x : R) ->
      addR x zeroR == x
    add-inverse :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-one :
      (x : R) ->
      multiplyR x oneR == x
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    multiply-zero :
      (x : R) ->
      multiplyR x zeroR == zeroR
    no-zero-divisors :
      (x y : R) ->
      multiplyR x y == zeroR ->
      (x == zeroR) or (y == zeroR)

power :
  {a : Level} ->
  {R : Set a} ->
  IntegralDomain R ->
  R ->
  Nat ->
  R
power algebra x zero =
  IntegralDomain.oneR algebra
power algebra x (suc n) =
  IntegralDomain.multiplyR algebra x (power algebra x n)

monomialValue :
  {a : Level} ->
  {R : Set a} ->
  (algebra : IntegralDomain R) ->
  {n : Nat} ->
  Vector R n ->
  Vector Nat n ->
  R
monomialValue algebra vector-empty vector-empty =
  IntegralDomain.oneR algebra
monomialValue algebra
  (vector-cons value values)
  (vector-cons exponent exponents) =
  IntegralDomain.multiplyR algebra
    (power algebra value exponent)
    (monomialValue algebra values exponents)

record Polynomial
  {a : Level}
  {R : Set a}
  (algebra : IntegralDomain R)
  (n : Nat) :
  Set a where

  field
    coefficient :
      Vector Nat n ->
      R
    support :
      List (Vector Nat n)
    support-exact :
      (exponent : Vector Nat n) ->
      Member exponent support
      iff
      (coefficient exponent not-equal IntegralDomain.zeroR algebra)
    support-no-duplicates :
      NoDuplicates support

evaluateSupport :
  {a : Level} ->
  {R : Set a} ->
  (algebra : IntegralDomain R) ->
  {n : Nat} ->
  (coefficient : Vector Nat n -> R) ->
  List (Vector Nat n) ->
  Vector R n ->
  R
evaluateSupport algebra coefficient [] values =
  IntegralDomain.zeroR algebra
evaluateSupport algebra coefficient
  (exponent ∷ support) values =
  IntegralDomain.addR algebra
    (IntegralDomain.multiplyR algebra
      (coefficient exponent)
      (monomialValue algebra values exponent))
    (evaluateSupport algebra coefficient support values)

evaluate :
  {a : Level} ->
  {R : Set a} ->
  (algebra : IntegralDomain R) ->
  {n : Nat} ->
  Polynomial algebra n ->
  Vector R n ->
  R
evaluate algebra polynomial values =
  evaluateSupport algebra
    (Polynomial.coefficient polynomial)
    (Polynomial.support polynomial)
    values

NonzeroPolynomial :
  {a : Level} ->
  {R : Set a} ->
  {algebra : IntegralDomain R} ->
  {n : Nat} ->
  Polynomial algebra n ->
  Set a
NonzeroPolynomial {algebra = algebra} polynomial =
  Σ _
    (\ exponent ->
      Polynomial.coefficient polynomial exponent
      not-equal
      IntegralDomain.zeroR algebra)

prependAssignments :
  {a : Level} ->
  {A : Set a} ->
  {n : Nat} ->
  A ->
  List (Vector A n) ->
  List (Vector A (suc n))
prependAssignments x [] =
  []
prependAssignments x (values ∷ assignments) =
  vector-cons x values ∷ prependAssignments x assignments

chooseHeads :
  {a : Level} ->
  {A : Set a} ->
  {n : Nat} ->
  List A ->
  List (Vector A n) ->
  List (Vector A (suc n))
chooseHeads [] tails =
  []
chooseHeads (x ∷ xs) tails =
  append
    (prependAssignments x tails)
    (chooseHeads xs tails)
  where
  append :
    {b : Level} ->
    {B : Set b} ->
    List B ->
    List B ->
    List B
  append [] ys =
    ys
  append (y ∷ ys) zs =
    y ∷ append ys zs

cartesianAssignments :
  {a : Level} ->
  {A : Set a} ->
  {n : Nat} ->
  Vector (FiniteSubset A) n ->
  List (Vector A n)
cartesianAssignments vector-empty =
  vector-empty ∷ []
cartesianAssignments (vector-cons subset subsets) =
  chooseHeads
    (FiniteSubset.elements subset)
    (cartesianAssignments subsets)

countZeros :
  {a : Level} ->
  {R : Set a} ->
  (algebra : IntegralDomain R) ->
  DecidableEquality R ->
  {n : Nat} ->
  Polynomial algebra n ->
  List (Vector R n) ->
  Nat
countZeros algebra decidableEquality polynomial [] =
  zero
countZeros algebra decidableEquality polynomial (values ∷ assignments)
  with decidableEquality
    (evaluate algebra polynomial values)
    (IntegralDomain.zeroR algebra)
... | yes equality =
  suc (countZeros algebra decidableEquality polynomial assignments)
... | no inequality =
  countZeros algebra decidableEquality polynomial assignments

record Fraction : Set where
  constructor fraction
  field
    numerator           : Nat
    denominatorMinusOne : Nat

fractionDenominator :
  Fraction ->
  Nat
fractionDenominator value =
  suc (Fraction.denominatorMinusOne value)

zeroFraction :
  Fraction
zeroFraction =
  fraction zero zero

divideNaturals :
  Nat ->
  Nat ->
  Fraction
divideNaturals numerator zero =
  zeroFraction
divideNaturals numerator (suc denominatorMinusOne) =
  fraction numerator denominatorMinusOne

addFractions :
  Fraction ->
  Fraction ->
  Fraction
addFractions first second =
  fraction
    ((Fraction.numerator first * fractionDenominator second) +
     (Fraction.numerator second * fractionDenominator first))
    ((Fraction.denominatorMinusOne first +
      Fraction.denominatorMinusOne second) +
     (Fraction.denominatorMinusOne first *
      Fraction.denominatorMinusOne second))

FractionLessOrEqual :
  Fraction ->
  Fraction ->
  Set
FractionLessOrEqual first second =
  (Fraction.numerator first * fractionDenominator second)
  less-or-equal
  (Fraction.numerator second * fractionDenominator first)

fractionLessOrEqualBool :
  Fraction ->
  Fraction ->
  Bool
fractionLessOrEqualBool first second =
  lessOrEqualBool
    (Fraction.numerator first * fractionDenominator second)
    (Fraction.numerator second * fractionDenominator first)

maxFraction :
  Fraction ->
  Fraction ->
  Fraction
maxFraction first second with fractionLessOrEqualBool first second
... | true =
  second
... | false =
  first

sumCoordinateRatios :
  {a : Level} ->
  {R : Set a} ->
  {n : Nat} ->
  Vector Nat n ->
  Vector (FiniteSubset R) n ->
  Fraction
sumCoordinateRatios vector-empty vector-empty =
  zeroFraction
sumCoordinateRatios
  (vector-cons exponent exponents)
  (vector-cons subset subsets) =
  addFractions
    (divideNaturals exponent (cardinality subset))
    (sumCoordinateRatios exponents subsets)

supportSupremum :
  {a : Level} ->
  {R : Set a} ->
  {n : Nat} ->
  List (Vector Nat n) ->
  Vector (FiniteSubset R) n ->
  Fraction
supportSupremum [] subsets =
  zeroFraction
supportSupremum (exponent ∷ support) subsets =
  maxFraction
    (sumCoordinateRatios exponent subsets)
    (supportSupremum support subsets)

productCardinalities :
  {a : Level} ->
  {R : Set a} ->
  {n : Nat} ->
  Vector (FiniteSubset R) n ->
  Nat
productCardinalities vector-empty =
  suc zero
productCardinalities (vector-cons subset subsets) =
  cardinality subset * productCardinalities subsets

schwartz-zippel-theorem : Setω
schwartz-zippel-theorem =
  {a : Level} ->
  (R : Set a) ->
  (algebra : IntegralDomain R) ->
  (decidableEquality : DecidableEquality R) ->
  (n : Nat) ->
  (polynomial : Polynomial algebra n) ->
  NonzeroPolynomial polynomial ->
  (subsets : Vector (FiniteSubset R) n) ->
  FractionLessOrEqual
    (divideNaturals
      (countZeros algebra decidableEquality polynomial
        (cartesianAssignments subsets))
      (productCardinalities subsets))
    (supportSupremum
      (Polynomial.support polynomial)
      subsets)
