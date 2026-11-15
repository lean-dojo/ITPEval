-- Statement-only formalization of thousand-theorems corpus artifact Q656645,
-- "Hilbert's basis theorem": the univariate polynomial ring over a commutative
-- Noetherian ring is again Noetherian. This file contains no proof.

{-# OPTIONS --safe #-}

module Q656645_hilbert_s_basis_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _and_

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record CommutativeRing
  {a : Level}
  (R : Set a) :
  Set a where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR : R -> R

    add-associative :
      (x y z : R) ->
      addR (addR x y) z ≡ addR x (addR y z)
    add-commutative :
      (x y : R) ->
      addR x y ≡ addR y x
    add-zero-left :
      (x : R) ->
      addR zeroR x ≡ x
    add-zero-right :
      (x : R) ->
      addR x zeroR ≡ x
    add-inverse-left :
      (x : R) ->
      addR (negateR x) x ≡ zeroR
    add-inverse-right :
      (x : R) ->
      addR x (negateR x) ≡ zeroR

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-commutative :
      (x y : R) ->
      multiplyR x y ≡ multiplyR y x
    multiply-one-left :
      (x : R) ->
      multiplyR oneR x ≡ x
    multiply-one-right :
      (x : R) ->
      multiplyR x oneR ≡ x
    distribute-left :
      (x y z : R) ->
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    distribute-right :
      (x y z : R) ->
      multiplyR (addR x y) z ≡
      addR (multiplyR x z) (multiplyR y z)

record Ideal
  {a : Level}
  {R : Set a}
  (ring : CommutativeRing R) :
  Set (lsuc a) where

  field
    member : R -> Set a
    membership-propositional :
      (x : R) ->
      (u v : member x) ->
      u ≡ v
    contains-zero :
      member (CommutativeRing.zeroR ring)
    closed-under-addition :
      (x y : R) ->
      member x ->
      member y ->
      member (CommutativeRing.addR ring x y)
    closed-under-negation :
      (x : R) ->
      member x ->
      member (CommutativeRing.negateR ring x)
    absorbs-multiplication :
      (r x : R) ->
      member x ->
      member (CommutativeRing.multiplyR ring r x)

IdealIncludedIn :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  Ideal ring ->
  Ideal ring ->
  Set a
IdealIncludedIn {R = R} I J =
  (x : R) ->
  Ideal.member I x ->
  Ideal.member J x

data ContainsAll
  {a : Level}
  {R : Set a}
  {ring : CommutativeRing R}
  (I : Ideal ring) :
  List R ->
  Set a where

  contains-empty :
    ContainsAll I []

  contains-cons :
    {x : R} ->
    {xs : List R} ->
    Ideal.member I x ->
    ContainsAll I xs ->
    ContainsAll I (x ∷ xs)

GeneratesIdeal :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  List R ->
  Ideal ring ->
  Set (lsuc a)
GeneratesIdeal {ring = ring} generators I =
  ContainsAll I generators and
  ((J : Ideal ring) ->
    ContainsAll J generators ->
    IdealIncludedIn I J)

IsNoetherianRing :
  {a : Level} ->
  {R : Set a} ->
  CommutativeRing R ->
  Set (lsuc a)
IsNoetherianRing {R = R} ring =
  (I : Ideal ring) ->
  Σ (List R)
    (λ generators ->
      GeneratesIdeal generators I)

Polynomial :
  {a : Level} ->
  Set a ->
  Set a
Polynomial R =
  List R

coefficientAt :
  {a : Level} ->
  {R : Set a} ->
  CommutativeRing R ->
  Polynomial R ->
  Nat ->
  R
coefficientAt ring [] n =
  CommutativeRing.zeroR ring
coefficientAt ring (coefficient ∷ coefficients) zero =
  coefficient
coefficientAt ring (coefficient ∷ coefficients) (suc n) =
  coefficientAt ring coefficients n

PolynomialEqual :
  {a : Level} ->
  {R : Set a} ->
  CommutativeRing R ->
  Polynomial R ->
  Polynomial R ->
  Set a
PolynomialEqual ring left right =
  (n : Nat) ->
  coefficientAt ring left n ≡
  coefficientAt ring right n

addPolynomial :
  {a : Level} ->
  {R : Set a} ->
  CommutativeRing R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
addPolynomial ring [] right =
  right
addPolynomial ring left [] =
  left
addPolynomial ring (x ∷ xs) (y ∷ ys) =
  CommutativeRing.addR ring x y ∷
  addPolynomial ring xs ys

negatePolynomial :
  {a : Level} ->
  {R : Set a} ->
  CommutativeRing R ->
  Polynomial R ->
  Polynomial R
negatePolynomial ring [] =
  []
negatePolynomial ring (x ∷ xs) =
  CommutativeRing.negateR ring x ∷
  negatePolynomial ring xs

scalePolynomial :
  {a : Level} ->
  {R : Set a} ->
  CommutativeRing R ->
  R ->
  Polynomial R ->
  Polynomial R
scalePolynomial ring scalar [] =
  []
scalePolynomial ring scalar (x ∷ xs) =
  CommutativeRing.multiplyR ring scalar x ∷
  scalePolynomial ring scalar xs

multiplyPolynomial :
  {a : Level} ->
  {R : Set a} ->
  CommutativeRing R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
multiplyPolynomial ring [] right =
  []
multiplyPolynomial ring (x ∷ xs) right =
  addPolynomial ring
    (scalePolynomial ring x right)
    (CommutativeRing.zeroR ring ∷
     multiplyPolynomial ring xs right)

record PolynomialIdeal
  {a : Level}
  {R : Set a}
  (ring : CommutativeRing R) :
  Set (lsuc a) where

  field
    member :
      Polynomial R ->
      Set a
    membership-propositional :
      (polynomial : Polynomial R) ->
      (u v : member polynomial) ->
      u ≡ v
    respects-polynomial-equality :
      (left right : Polynomial R) ->
      PolynomialEqual ring left right ->
      member left ->
      member right
    contains-zero :
      member []
    closed-under-addition :
      (left right : Polynomial R) ->
      member left ->
      member right ->
      member (addPolynomial ring left right)
    closed-under-negation :
      (polynomial : Polynomial R) ->
      member polynomial ->
      member (negatePolynomial ring polynomial)
    absorbs-multiplication :
      (factor polynomial : Polynomial R) ->
      member polynomial ->
      member (multiplyPolynomial ring factor polynomial)

PolynomialIdealIncludedIn :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  PolynomialIdeal ring ->
  PolynomialIdeal ring ->
  Set a
PolynomialIdealIncludedIn {R = R} I J =
  (polynomial : Polynomial R) ->
  PolynomialIdeal.member I polynomial ->
  PolynomialIdeal.member J polynomial

data ContainsAllPolynomials
  {a : Level}
  {R : Set a}
  {ring : CommutativeRing R}
  (I : PolynomialIdeal ring) :
  List (Polynomial R) ->
  Set a where

  contains-no-polynomials :
    ContainsAllPolynomials I []

  contains-polynomial :
    {polynomial : Polynomial R} ->
    {polynomials : List (Polynomial R)} ->
    PolynomialIdeal.member I polynomial ->
    ContainsAllPolynomials I polynomials ->
    ContainsAllPolynomials I (polynomial ∷ polynomials)

GeneratesPolynomialIdeal :
  {a : Level} ->
  {R : Set a} ->
  {ring : CommutativeRing R} ->
  List (Polynomial R) ->
  PolynomialIdeal ring ->
  Set (lsuc a)
GeneratesPolynomialIdeal {ring = ring} generators I =
  ContainsAllPolynomials I generators and
  ((J : PolynomialIdeal ring) ->
    ContainsAllPolynomials J generators ->
    PolynomialIdealIncludedIn I J)

IsNoetherianPolynomialRing :
  {a : Level} ->
  {R : Set a} ->
  CommutativeRing R ->
  Set (lsuc a)
IsNoetherianPolynomialRing {R = R} ring =
  (I : PolynomialIdeal ring) ->
  Σ (List (Polynomial R))
    (λ generators ->
      GeneratesPolynomialIdeal generators I)

-- Lean: Polynomial.isNoetherianRing
hilbert-s-basis-theorem :
  (a : Level) ->
  Set (lsuc a)
hilbert-s-basis-theorem a =
  (R : Set a) ->
  (ring : CommutativeRing R) ->
  IsNoetherianRing ring ->
  IsNoetherianPolynomialRing ring
