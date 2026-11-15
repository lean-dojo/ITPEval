-- Statement-only formalization of thousand-theorems corpus artifact Q6783821,
-- "Mason–Stothers theorem": the polynomial ABC degree bounds for three
-- nonzero coprime-summand polynomials over an arbitrary field, with the
-- alternative that all three formal derivatives vanish. This file contains no proof.

{-# OPTIONS --safe #-}

module Q6783821_mason_stothers_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_ _iff_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

_≠_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x ≠ y =
  Not (x ≡ y)

data Dec
  {a : Level}
  (P : Set a) :
  Set a where

  yes : P -> Dec P
  no  : Not P -> Dec P

record _and_
  {a b : Level}
  (P : Set a)
  (Q : Set b) :
  Set (a ⊔ b) where

  field
    first  : P
    second : Q

data _or_
  {a b : Level}
  (P : Set a)
  (Q : Set b) :
  Set (a ⊔ b) where

  left  : P -> P or Q
  right : Q -> P or Q

record _iff_
  {a b : Level}
  (P : Set a)
  (Q : Set b) :
  Set (a ⊔ b) where

  field
    forward  : P -> Q
    backward : Q -> P

data LessOrEqual : Nat -> Nat -> Set where
  zero-less-or-equal :
    {n : Nat} ->
    LessOrEqual zero n
  successor-less-or-equal :
    {m n : Nat} ->
    LessOrEqual m n ->
    LessOrEqual (suc m) (suc n)

record Field
  {a : Level}
  (K : Set a) :
  Set a where

  field
    zeroF oneF : K
    addF multiplyF : K -> K -> K
    negateF inverseF : K -> K

    decidable-equality :
      (x y : K) ->
      Dec (x ≡ y)

    one-not-zero :
      oneF ≠ zeroF

    add-commutative :
      (x y : K) ->
      addF x y ≡ addF y x
    add-associative :
      (x y z : K) ->
      addF (addF x y) z ≡ addF x (addF y z)
    add-zero :
      (x : K) ->
      addF x zeroF ≡ x
    add-inverse :
      (x : K) ->
      addF x (negateF x) ≡ zeroF

    multiply-commutative :
      (x y : K) ->
      multiplyF x y ≡ multiplyF y x
    multiply-associative :
      (x y z : K) ->
      multiplyF (multiplyF x y) z ≡
      multiplyF x (multiplyF y z)
    multiply-one :
      (x : K) ->
      multiplyF x oneF ≡ x
    multiply-zero :
      (x : K) ->
      multiplyF x zeroF ≡ zeroF
    distribute :
      (x y z : K) ->
      multiplyF x (addF y z) ≡
      addF (multiplyF x y) (multiplyF x z)

    inverse-zero :
      inverseF zeroF ≡ zeroF
    multiply-inverse :
      (x : K) ->
      x ≠ zeroF ->
      multiplyF x (inverseF x) ≡ oneF

open Field

record Polynomial
  {a : Level}
  {K : Set a}
  (fieldStructure : Field K) :
  Set a where

  field
    coefficient : Nat -> K
    bound : Nat
    zero-after-bound :
      (offset : Nat) ->
      coefficient (bound + suc offset) ≡ zeroF fieldStructure

open Polynomial

oneCoefficient :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  Nat ->
  K
oneCoefficient fieldStructure zero =
  oneF fieldStructure
oneCoefficient fieldStructure (suc n) =
  zeroF fieldStructure

multiplyCoefficient :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  (Nat -> K) ->
  (Nat -> K) ->
  Nat ->
  K
multiplyCoefficient fieldStructure leftCoefficients rightCoefficients zero =
  multiplyF fieldStructure
    (leftCoefficients zero)
    (rightCoefficients zero)
multiplyCoefficient fieldStructure leftCoefficients rightCoefficients (suc n) =
  addF fieldStructure
    (multiplyF fieldStructure
      (leftCoefficients zero)
      (rightCoefficients (suc n)))
    (multiplyCoefficient fieldStructure
      (λ i -> leftCoefficients (suc i))
      rightCoefficients
      n)

natScale :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  Nat ->
  K ->
  K
natScale fieldStructure zero x =
  zeroF fieldStructure
natScale fieldStructure (suc n) x =
  addF fieldStructure x (natScale fieldStructure n x)

NonzeroPolynomial :
  {a : Level} ->
  {K : Set a} ->
  {fieldStructure : Field K} ->
  Polynomial fieldStructure ->
  Set a
NonzeroPolynomial {fieldStructure = fieldStructure} polynomial =
  Σ Nat
    (λ n ->
      coefficient polynomial n ≠ zeroF fieldStructure)

DegreeOf :
  {a : Level} ->
  {K : Set a} ->
  {fieldStructure : Field K} ->
  Polynomial fieldStructure ->
  Nat ->
  Set a
DegreeOf {fieldStructure = fieldStructure} polynomial degree =
  (coefficient polynomial degree ≠ zeroF fieldStructure)
  and
  ((offset : Nat) ->
    coefficient polynomial (degree + suc offset) ≡ zeroF fieldStructure)

ProductEqual :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  Polynomial fieldStructure ->
  (Nat -> K) ->
  Set a
ProductEqual fieldStructure leftPolynomial rightPolynomial result =
  (n : Nat) ->
  result n ≡
  multiplyCoefficient fieldStructure
    (coefficient leftPolynomial)
    (coefficient rightPolynomial)
    n

Divides :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  (Nat -> K) ->
  Set a
Divides fieldStructure divisor dividend =
  Σ (Polynomial fieldStructure)
    (λ quotient ->
      ProductEqual fieldStructure divisor quotient dividend)

UnitPolynomial :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  Set a
UnitPolynomial fieldStructure polynomial =
  Σ (Polynomial fieldStructure)
    (λ inversePolynomial ->
      ProductEqual fieldStructure
        polynomial
        inversePolynomial
        (oneCoefficient fieldStructure))

record Irreducible
  {a : Level}
  {K : Set a}
  (fieldStructure : Field K)
  (polynomial : Polynomial fieldStructure) :
  Set a where

  field
    nonzero :
      NonzeroPolynomial polynomial
    nonunit :
      Not (UnitPolynomial fieldStructure polynomial)
    factor-is-trivial :
      (leftPolynomial rightPolynomial : Polynomial fieldStructure) ->
      ProductEqual fieldStructure
        leftPolynomial
        rightPolynomial
        (coefficient polynomial) ->
      (UnitPolynomial fieldStructure leftPolynomial) or
      (UnitPolynomial fieldStructure rightPolynomial)

IsCoprime :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  Polynomial fieldStructure ->
  Set a
IsCoprime fieldStructure leftPolynomial rightPolynomial =
  Σ (Polynomial fieldStructure)
    (λ leftCoefficient ->
      Σ (Polynomial fieldStructure)
        (λ rightCoefficient ->
          (n : Nat) ->
          addF fieldStructure
            (multiplyCoefficient fieldStructure
              (coefficient leftCoefficient)
              (coefficient leftPolynomial)
              n)
            (multiplyCoefficient fieldStructure
              (coefficient rightCoefficient)
              (coefficient rightPolynomial)
              n)
          ≡
          oneCoefficient fieldStructure n))

SquareDivides :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  Polynomial fieldStructure ->
  Set a
SquareDivides fieldStructure divisor dividend =
  Σ (Polynomial fieldStructure)
    (λ quotient ->
      (n : Nat) ->
      coefficient dividend n ≡
      multiplyCoefficient fieldStructure
        (multiplyCoefficient fieldStructure
          (coefficient divisor)
          (coefficient divisor))
        (coefficient quotient)
        n)

SquareFree :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  Set a
SquareFree fieldStructure polynomial =
  (divisor : Polynomial fieldStructure) ->
  Irreducible fieldStructure divisor ->
  Not (SquareDivides fieldStructure divisor polynomial)

SameIrreducibleDivisors :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  (Nat -> K) ->
  Polynomial fieldStructure ->
  Set a
SameIrreducibleDivisors fieldStructure source radicalPolynomial =
  (divisor : Polynomial fieldStructure) ->
  Irreducible fieldStructure divisor ->
  (Divides fieldStructure divisor source)
  iff
  (Divides fieldStructure divisor (coefficient radicalPolynomial))

MonicOfDegree :
  {a : Level} ->
  {K : Set a} ->
  {fieldStructure : Field K} ->
  Polynomial fieldStructure ->
  Nat ->
  Set a
MonicOfDegree {fieldStructure = fieldStructure} polynomial degree =
  DegreeOf polynomial degree
  and
  (coefficient polynomial degree ≡ oneF fieldStructure)

RadicalDegree :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  (Nat -> K) ->
  Nat ->
  Set a
RadicalDegree fieldStructure source degree =
  Σ (Polynomial fieldStructure)
    (λ radicalPolynomial ->
      MonicOfDegree radicalPolynomial degree
      and
      SquareFree fieldStructure radicalPolynomial
      and
      SameIrreducibleDivisors
        fieldStructure
        source
        radicalPolynomial)

tripleProductCoefficient :
  {a : Level} ->
  {K : Set a} ->
  {fieldStructure : Field K} ->
  Polynomial fieldStructure ->
  Polynomial fieldStructure ->
  Polynomial fieldStructure ->
  Nat ->
  K
tripleProductCoefficient {fieldStructure = fieldStructure}
  firstPolynomial secondPolynomial thirdPolynomial n =
  multiplyCoefficient fieldStructure
    (multiplyCoefficient fieldStructure
      (coefficient firstPolynomial)
      (coefficient secondPolynomial))
    (coefficient thirdPolynomial)
    n

SumIsZero :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  Polynomial fieldStructure ->
  Polynomial fieldStructure ->
  Set a
SumIsZero fieldStructure firstPolynomial secondPolynomial thirdPolynomial =
  (n : Nat) ->
  addF fieldStructure
    (addF fieldStructure
      (coefficient firstPolynomial n)
      (coefficient secondPolynomial n))
    (coefficient thirdPolynomial n)
  ≡
  zeroF fieldStructure

DerivativeIsZero :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  Set a
DerivativeIsZero fieldStructure polynomial =
  (n : Nat) ->
  natScale fieldStructure
    (suc n)
    (coefficient polynomial (suc n))
  ≡
  zeroF fieldStructure

DegreeBound :
  {a : Level} ->
  {K : Set a} ->
  (fieldStructure : Field K) ->
  Polynomial fieldStructure ->
  Nat ->
  Set a
DegreeBound fieldStructure polynomial radicalDegree =
  Σ Nat
    (λ polynomialDegree ->
      DegreeOf polynomial polynomialDegree
      and
      LessOrEqual (suc polynomialDegree) radicalDegree)

mason-stothers-theorem :
  (a : Level) ->
  Set (lsuc a)
mason-stothers-theorem a =
  (K : Set a) ->
  (fieldStructure : Field K) ->
  (firstPolynomial secondPolynomial thirdPolynomial :
    Polynomial fieldStructure) ->
  NonzeroPolynomial firstPolynomial ->
  NonzeroPolynomial secondPolynomial ->
  NonzeroPolynomial thirdPolynomial ->
  IsCoprime fieldStructure firstPolynomial secondPolynomial ->
  SumIsZero
    fieldStructure
    firstPolynomial
    secondPolynomial
    thirdPolynomial ->
  let product =
        tripleProductCoefficient
          firstPolynomial
          secondPolynomial
          thirdPolynomial
  in
  (Σ Nat
    (λ radicalDegree ->
      RadicalDegree fieldStructure product radicalDegree
      and
      (DegreeBound fieldStructure firstPolynomial radicalDegree)
      and
      (DegreeBound fieldStructure secondPolynomial radicalDegree)
      and
      (DegreeBound fieldStructure thirdPolynomial radicalDegree)))
  or
  ((DerivativeIsZero fieldStructure firstPolynomial)
    and
    (DerivativeIsZero fieldStructure secondPolynomial)
    and
    (DerivativeIsZero fieldStructure thirdPolynomial))
