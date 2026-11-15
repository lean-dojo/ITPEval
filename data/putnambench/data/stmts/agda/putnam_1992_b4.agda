-- Statement-only formalization of PutnamBench corpus artifact putnam_1992_b4
-- (putnambench__agda__putnam_1992_b4): the least numerator degree after
-- differentiating p(x)/(x^3-x) 1992 times. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))
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
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

DifferenceQuotient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  R
DifferenceQuotient reals function point x =
  divide reals
    (subtract reals (function x) (function point))
    (subtract reals x point)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative epsilon
          (DifferenceQuotient reals function point x)))

DerivativeValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeValue {R} reals function point value =
  DerivativeAt reals function point value
  or
  (value == zeroR reals
  and
  Not
    (Exists R
      (\ candidate ->
        DerivativeAt reals function point candidate)))

TotalDerivative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  (R -> R) ->
  Set
TotalDerivative {R} reals function derivative =
  (x : R) ->
  DerivativeValue reals function x (derivative x)

EqFunction :
  {A B : Set} ->
  (A -> B) ->
  (A -> B) ->
  Set
EqFunction f g =
  (x : _) ->
  f x == g x

IteratedDerivative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (R -> R) ->
  (R -> R) ->
  Set
IteratedDerivative reals zero function result =
  EqFunction function result
IteratedDerivative {R = R} reals (suc n) function result =
  Exists (R -> R)
    (\ previous ->
      IteratedDerivative reals n function previous
      and
      TotalDerivative reals previous result)

module Putnam1992B4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Polynomial : Set
  Polynomial =
    List R

  coefficient : Polynomial -> Nat -> R
  coefficient [] n =
    zeroR reals
  coefficient (c ∷ coefficients) zero =
    c
  coefficient (c ∷ coefficients) (suc n) =
    coefficient coefficients n

  PolynomialEqual :
    Polynomial ->
    Polynomial ->
    Set
  PolynomialEqual p q =
    (n : Nat) ->
    coefficient p n == coefficient q n

  zeroPolynomial : Polynomial
  zeroPolynomial =
    []

  onePolynomial : Polynomial
  onePolynomial =
    oneR reals ∷ []

  X : Polynomial
  X =
    zeroR reals ∷ oneR reals ∷ []

  addPolynomial :
    Polynomial ->
    Polynomial ->
    Polynomial
  addPolynomial [] q =
    q
  addPolynomial p [] =
    p
  addPolynomial (a ∷ p) (b ∷ q) =
    add reals a b ∷ addPolynomial p q

  negatePolynomial :
    Polynomial ->
    Polynomial
  negatePolynomial [] =
    []
  negatePolynomial (a ∷ p) =
    negate reals a ∷ negatePolynomial p

  subtractPolynomial :
    Polynomial ->
    Polynomial ->
    Polynomial
  subtractPolynomial p q =
    addPolynomial p (negatePolynomial q)

  scalePolynomial :
    R ->
    Polynomial ->
    Polynomial
  scalePolynomial scalar [] =
    []
  scalePolynomial scalar (a ∷ p) =
    multiply reals scalar a ∷ scalePolynomial scalar p

  multiplyPolynomial :
    Polynomial ->
    Polynomial ->
    Polynomial
  multiplyPolynomial [] q =
    []
  multiplyPolynomial (a ∷ p) q =
    addPolynomial
      (scalePolynomial a q)
      (zeroR reals ∷ multiplyPolynomial p q)

  powerPolynomial :
    Polynomial ->
    Nat ->
    Polynomial
  powerPolynomial p zero =
    onePolynomial
  powerPolynomial p (suc n) =
    multiplyPolynomial p (powerPolynomial p n)

  cubicMinusX : Polynomial
  cubicMinusX =
    subtractPolynomial (powerPolynomial X 3) X

  evaluatePolynomial :
    Polynomial ->
    R ->
    R
  evaluatePolynomial [] x =
    zeroR reals
  evaluatePolynomial (a ∷ p) x =
    add reals a
      (multiply reals x (evaluatePolynomial p x))

  PolynomialNonzero :
    Polynomial ->
    Set
  PolynomialNonzero p =
    Not (PolynomialEqual p zeroPolynomial)

  Degree :
    Polynomial ->
    Nat ->
    Set
  Degree p n =
    (PolynomialEqual p zeroPolynomial and n == zero)
    or
    (coefficient p n != zeroR reals
    and
    ((k : Nat) ->
      n <N k ->
      coefficient p k == zeroR reals))

  Divides :
    Polynomial ->
    Polynomial ->
    Set
  Divides divisor dividend =
    Exists Polynomial
      (\ quotient ->
        PolynomialEqual dividend
          (multiplyPolynomial divisor quotient))

  Coprime :
    Polynomial ->
    Polynomial ->
    Set
  Coprime p q =
    (commonDivisor : Polynomial) ->
    Divides commonDivisor p ->
    Divides commonDivisor q ->
    Degree commonDivisor zero

  Valid :
    Polynomial ->
    Set
  Valid p =
    PolynomialNonzero p
    and
    Exists Nat
      (\ degree ->
        Degree p degree
        and
        degree <N 1992)
    and
    Coprime p cubicMinusX

  cubicDenominatorValue :
    R ->
    R
  cubicDenominatorValue x =
    subtract reals
      (multiply reals x (multiply reals x x))
      x

  initialFunction :
    Polynomial ->
    R ->
    R
  initialFunction p x =
    divide reals
      (evaluatePolynomial p x)
      (cubicDenominatorValue x)

  rationalFunction :
    Polynomial ->
    Polynomial ->
    R ->
    R
  rationalFunction numerator denominator x =
    divide reals
      (evaluatePolynomial numerator x)
      (evaluatePolynomial denominator x)

  Pair :
    Polynomial ->
    Polynomial ->
    Set
  Pair p f =
    Exists Polynomial
      (\ g ->
        PolynomialNonzero g
        and
        Exists (R -> R)
          (\ derivative1992 ->
            IteratedDerivative reals 1992
              (initialFunction p)
              derivative1992
            and
            ((x : R) ->
              x != negate reals (oneR reals) ->
              x != zeroR reals ->
              x != oneR reals ->
              evaluatePolynomial g x != zeroR reals ->
              derivative1992 x == rationalFunction f g x)))

  AttainableDegree :
    Nat ->
    Set
  AttainableDegree degree =
    Exists Polynomial
      (\ p ->
        Exists Polynomial
          (\ f ->
            Valid p
            and
            Pair p f
            and
            Degree f degree))

  IsLeast :
    (Nat -> Set) ->
    Nat ->
    Set
  IsLeast property least =
    property least
    and
    ((candidate : Nat) ->
      property candidate ->
      least <=N candidate)

  proposition : Set
  proposition =
    IsLeast AttainableDegree 3984

putnam-1992-b4 : Set1
putnam-1992-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1992B4Statement.proposition reals
