-- Statement-only formalization of PutnamBench corpus artifact putnam_2019_a5
-- (putnambench__agda__putnam_2019_a5): the greatest multiplicity of x - 1
-- in the polynomial over F_p whose coefficients are quadratic-character
-- powers is (p - 1) / 2. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)

infix 4 _!=_ _<=N_ _<N_
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

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

Odd : Nat -> Set
Odd n =
  Exists Nat
    (\ k -> n == suc (twoN * k))

DividesNat : Nat -> Nat -> Set
DividesNat divisor number =
  Exists Nat
    (\ quotient -> number == divisor * quotient)

Prime : Nat -> Set
Prime n =
  twoN <=N n
  and
  ((divisor : Nat) ->
    DividesNat divisor n ->
    divisor == oneN or divisor == n)

record PrimeFieldModel
  (p : Nat)
  (F : Set) :
  Set1 where

  field
    zeroF oneF : F
    add multiply : F -> F -> F
    negate inverse : F -> F
    residue : Nat -> F

    one-not-zero :
      oneF != zeroF

    add-commutative :
      (x y : F) ->
      add x y == add y x
    add-associative :
      (x y z : F) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : F) ->
      add x zeroF == x
    add-inverse :
      (x : F) ->
      add x (negate x) == zeroF

    multiply-commutative :
      (x y : F) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : F) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : F) ->
      multiply x oneF == x
    multiply-zero :
      (x : F) ->
      multiply x zeroF == zeroF
    distribute :
      (x y z : F) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroF == zeroF
    multiply-inverse :
      (x : F) ->
      x != zeroF ->
      multiply x (inverse x) == oneF

    residue-zero :
      residue zero == zeroF
    residue-successor :
      (n : Nat) ->
      residue (suc n) == add (residue n) oneF
    characteristic-p :
      residue p == zeroF
    residue-complete :
      (x : F) ->
      Exists Nat
        (\ i ->
          i <N p
          and
          residue i == x)
    residue-injective :
      (i j : Nat) ->
      i <N p ->
      j <N p ->
      residue i == residue j ->
      i == j

open PrimeFieldModel

fieldPower :
  {p : Nat} ->
  {F : Set} ->
  PrimeFieldModel p F ->
  F ->
  Nat ->
  F
fieldPower algebra x zero =
  oneF algebra
fieldPower algebra x (suc n) =
  multiply algebra
    (fieldPower algebra x n)
    x

sumThrough :
  {p : Nat} ->
  {F : Set} ->
  PrimeFieldModel p F ->
  Nat ->
  (Nat -> F) ->
  F
sumThrough algebra zero term =
  term zero
sumThrough algebra (suc n) term =
  add algebra
    (sumThrough algebra n term)
    (term (suc n))

record PolynomialAlgebra
  {p : Nat}
  {F : Set}
  (algebra : PrimeFieldModel p F)
  (P : Set) :
  Set1 where

  field
    zeroP oneP XP : P
    addP multiplyP : P -> P -> P
    negateP : P -> P
    coefficient : P -> Nat -> F

    finite-support :
      (polynomial : P) ->
      Exists Nat
        (\ bound ->
          (n : Nat) ->
          bound <N n ->
          coefficient polynomial n == zeroF algebra)

    coefficient-extensionality :
      (leftPolynomial rightPolynomial : P) ->
      ((n : Nat) ->
        coefficient leftPolynomial n ==
        coefficient rightPolynomial n) ->
      leftPolynomial == rightPolynomial

    coefficient-zero :
      (n : Nat) ->
      coefficient zeroP n == zeroF algebra
    coefficient-one-zero :
      coefficient oneP zero == oneF algebra
    coefficient-one-successor :
      (n : Nat) ->
      coefficient oneP (suc n) == zeroF algebra
    coefficient-X-zero :
      coefficient XP zero == zeroF algebra
    coefficient-X-one :
      coefficient XP oneN == oneF algebra
    coefficient-X-above-one :
      (n : Nat) ->
      coefficient XP (suc (suc n)) == zeroF algebra

    coefficient-add :
      (leftPolynomial rightPolynomial : P) ->
      (n : Nat) ->
      coefficient (addP leftPolynomial rightPolynomial) n ==
      add algebra
        (coefficient leftPolynomial n)
        (coefficient rightPolynomial n)
    coefficient-negate :
      (polynomial : P) ->
      (n : Nat) ->
      coefficient (negateP polynomial) n ==
      negate algebra (coefficient polynomial n)
    coefficient-multiply :
      (leftPolynomial rightPolynomial : P) ->
      (n : Nat) ->
      coefficient (multiplyP leftPolynomial rightPolynomial) n ==
      sumThrough algebra n
        (\ i ->
          multiply algebra
            (coefficient leftPolynomial i)
            (coefficient rightPolynomial (n - i)))

open PolynomialAlgebra

polynomialPower :
  {p : Nat} ->
  {F P : Set} ->
  {algebra : PrimeFieldModel p F} ->
  PolynomialAlgebra algebra P ->
  P ->
  Nat ->
  P
polynomialPower polynomials polynomial zero =
  oneP polynomials
polynomialPower polynomials polynomial (suc n) =
  multiplyP polynomials
    (polynomialPower polynomials polynomial n)
    polynomial

xMinusOne :
  {p : Nat} ->
  {F P : Set} ->
  {algebra : PrimeFieldModel p F} ->
  PolynomialAlgebra algebra P ->
  P
xMinusOne polynomials =
  addP polynomials
    (XP polynomials)
    (negateP polynomials (oneP polynomials))

PolynomialDivides :
  {p : Nat} ->
  {F P : Set} ->
  {algebra : PrimeFieldModel p F} ->
  PolynomialAlgebra algebra P ->
  P ->
  P ->
  Set
PolynomialDivides {P = P} polynomials divisor dividend =
  Exists P
    (\ quotient ->
      dividend ==
      multiplyP polynomials divisor quotient)

QuadraticCharacterPolynomial :
  {p : Nat} ->
  {F P : Set} ->
  (algebra : PrimeFieldModel p F) ->
  (polynomials : PolynomialAlgebra algebra P) ->
  P ->
  Set
QuadraticCharacterPolynomial {p} algebra polynomials q =
  coefficient polynomials q zero == zeroF algebra
  and
  ((k : Nat) ->
    oneN <=N k ->
    k <N p ->
    coefficient polynomials q k ==
    fieldPower algebra (residue algebra k) (half p))
  and
  ((k : Nat) ->
    p <=N k ->
    coefficient polynomials q k == zeroF algebra)

record IsGreatestDivisibilityExponent
  {p : Nat}
  {F P : Set}
  {algebra : PrimeFieldModel p F}
  (polynomials : PolynomialAlgebra algebra P)
  (q : P)
  (greatest : Nat) :
  Set where

  field
    attained :
      PolynomialDivides polynomials
        (polynomialPower polynomials
          (xMinusOne polynomials)
          greatest)
        q

    upper-bound :
      (n : Nat) ->
      PolynomialDivides polynomials
        (polynomialPower polynomials
          (xMinusOne polynomials)
          n)
        q ->
      n <=N greatest

putnam-2019-a5 : Set1
putnam-2019-a5 =
  (p : Nat) ->
  Odd p ->
  Prime p ->
  (F P : Set) ->
  (algebra : PrimeFieldModel p F) ->
  (polynomials : PolynomialAlgebra algebra P) ->
  (q : P) ->
  QuadraticCharacterPolynomial algebra polynomials q ->
  IsGreatestDivisibilityExponent polynomials q (half p)
