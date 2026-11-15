-- Statement-only formalization of "Insolvability of General Higher Degree Equations
-- (Abel-Ruffini)" from Hundred Theorems item 016. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 3 _∧_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

record Field (F : Set) : Set₁ where
  field
    zeroF oneF : F
    add multiply : F → F → F
    negate inverse : F → F
    fromNat : Nat → F

    one-not-zero :
      oneF ≠ zeroF

    add-commutative :
      (x y : F) → add x y ≡ add y x
    add-associative :
      (x y z : F) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : F) → add x zeroF ≡ x
    add-inverse :
      (x : F) → add x (negate x) ≡ zeroF

    multiply-commutative :
      (x y : F) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : F) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : F) → multiply x oneF ≡ x
    multiply-zero :
      (x : F) → multiply x zeroF ≡ zeroF
    distribute :
      (x y z : F) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroF ≡ zeroF
    multiply-inverse :
      (x : F) →
      x ≠ zeroF →
      multiply x (inverse x) ≡ oneF

    fromNat-zero :
      fromNat zero ≡ zeroF
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneF
    characteristic-zero :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

power :
  {F : Set} →
  Field F →
  F →
  Nat →
  F
power algebra x zero =
  Field.oneF algebra
power algebra x (suc n) =
  Field.multiply algebra x (power algebra x n)

evaluate :
  {F : Set} →
  Field F →
  List F →
  F →
  F
evaluate algebra [] x =
  Field.zeroF algebra
evaluate algebra (coefficient ∷ coefficients) x =
  Field.add algebra coefficient
    (Field.multiply algebra x (evaluate algebra coefficients x))

data HasNonzeroCoefficient
  {F : Set}
  (algebra : Field F) :
  List F → Set where

  here :
    {coefficient : F} {coefficients : List F} →
    coefficient ≠ Field.zeroF algebra →
    HasNonzeroCoefficient algebra (coefficient ∷ coefficients)

  there :
    {coefficient : F} {coefficients : List F} →
    HasNonzeroCoefficient algebra coefficients →
    HasNonzeroCoefficient algebra (coefficient ∷ coefficients)

Nonconstant :
  {F : Set} →
  Field F →
  List F →
  Set
Nonconstant algebra [] = ⊥
Nonconstant algebra (coefficient ∷ coefficients) =
  HasNonzeroCoefficient algebra coefficients

record ComplexNumberModel (C : Set) : Set₁ where
  field
    algebra : Field C

    algebraically-closed :
      (coefficients : List C) →
      Nonconstant algebra coefficients →
      Σ C
        (λ z →
          evaluate algebra coefficients z ≡
          Field.zeroF algebra)

fieldOf :
  {C : Set} →
  ComplexNumberModel C →
  Field C
fieldOf = ComplexNumberModel.algebra

fromInt :
  {F : Set} →
  Field F →
  Int →
  F
fromInt algebra (pos n) =
  Field.fromNat algebra n
fromInt algebra (negsuc n) =
  Field.negate algebra
    (Field.fromNat algebra (suc n))

record Rational : Set where
  constructor fraction
  field
    numerator            : Int
    denominatorMinusOne : Nat

toField :
  {F : Set} →
  Field F →
  Rational →
  F
toField algebra q =
  Field.multiply algebra
    (fromInt algebra (Rational.numerator q))
    (Field.inverse algebra
      (Field.fromNat algebra
        (suc (Rational.denominatorMinusOne q))))

data HasNonzeroRationalCoefficient :
  List Rational → Set where

  rational-here :
    {coefficient : Rational}
    {coefficients : List Rational} →
    Rational.numerator coefficient ≠ pos zero →
    HasNonzeroRationalCoefficient
      (coefficient ∷ coefficients)

  rational-there :
    {coefficient : Rational}
    {coefficients : List Rational} →
    HasNonzeroRationalCoefficient coefficients →
    HasNonzeroRationalCoefficient
      (coefficient ∷ coefficients)

evaluateRationalPolynomial :
  {C : Set} →
  ComplexNumberModel C →
  List Rational →
  C →
  C
evaluateRationalPolynomial complex [] x =
  Field.zeroF (fieldOf complex)
evaluateRationalPolynomial complex
  (coefficient ∷ coefficients) x =
  Field.add (fieldOf complex)
    (toField (fieldOf complex) coefficient)
    (Field.multiply (fieldOf complex) x
      (evaluateRationalPolynomial complex coefficients x))

IsAlgebraic :
  {C : Set} →
  ComplexNumberModel C →
  C →
  Set
IsAlgebraic complex x =
  Σ (List Rational)
    (λ coefficients →
      HasNonzeroRationalCoefficient coefficients ∧
      evaluateRationalPolynomial complex coefficients x ≡
      Field.zeroF (fieldOf complex))

data RadicalExpression : Set where
  rationalConstant : Rational → RadicalExpression
  negative          : RadicalExpression → RadicalExpression
  reciprocal        : RadicalExpression → RadicalExpression
  sum               : RadicalExpression → RadicalExpression → RadicalExpression
  product           : RadicalExpression → RadicalExpression → RadicalExpression
  radicalRoot       : Nat → RadicalExpression → RadicalExpression

data EvaluatesTo
  {C : Set}
  (complex : ComplexNumberModel C) :
  RadicalExpression →
  C →
  Set where

  rational-value :
    (q : Rational) →
    EvaluatesTo complex
      (rationalConstant q)
      (toField (fieldOf complex) q)

  negative-value :
    {expression : RadicalExpression} {x : C} →
    EvaluatesTo complex expression x →
    EvaluatesTo complex
      (negative expression)
      (Field.negate (fieldOf complex) x)

  reciprocal-value :
    {expression : RadicalExpression} {x : C} →
    EvaluatesTo complex expression x →
    x ≠ Field.zeroF (fieldOf complex) →
    EvaluatesTo complex
      (reciprocal expression)
      (Field.inverse (fieldOf complex) x)

  sum-value :
    {left right : RadicalExpression} {x y : C} →
    EvaluatesTo complex left x →
    EvaluatesTo complex right y →
    EvaluatesTo complex
      (sum left right)
      (Field.add (fieldOf complex) x y)

  product-value :
    {left right : RadicalExpression} {x y : C} →
    EvaluatesTo complex left x →
    EvaluatesTo complex right y →
    EvaluatesTo complex
      (product left right)
      (Field.multiply (fieldOf complex) x y)

  radical-value :
    {degreeMinusOne : Nat}
    {expression : RadicalExpression}
    {radicand root : C} →
    EvaluatesTo complex expression radicand →
    power (fieldOf complex) root (suc degreeMinusOne) ≡ radicand →
    EvaluatesTo complex
      (radicalRoot degreeMinusOne expression)
      root

SolvableByRadicals :
  {C : Set} →
  ComplexNumberModel C →
  C →
  Set
SolvableByRadicals complex x =
  Σ RadicalExpression
    (λ expression → EvaluatesTo complex expression x)

quintic :
  {C : Set} →
  ComplexNumberModel C →
  C →
  C
quintic complex x =
  Field.add algebra
    (Field.add algebra
      (power algebra x 5)
      (Field.negate algebra
        (Field.multiply algebra
          (Field.fromNat algebra 4)
          x)))
    (Field.fromNat algebra 2)
  where
    algebra = fieldOf complex

IsQuinticRoot :
  {C : Set} →
  ComplexNumberModel C →
  C →
  Set
IsQuinticRoot complex x =
  quintic complex x ≡ Field.zeroF (fieldOf complex)

hundred-theorems-016 : Set₁
hundred-theorems-016 =
  (C : Set) →
  (complex : ComplexNumberModel C) →
  Σ C
    (λ x →
      IsQuinticRoot complex x ∧
      IsAlgebraic complex x ∧
      ¬ SolvableByRadicals complex x)
