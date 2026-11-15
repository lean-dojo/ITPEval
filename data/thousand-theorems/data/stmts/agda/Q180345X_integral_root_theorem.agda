-- Statement-only formalization of thousand-theorems corpus artifact Q180345X,
-- "Integral root theorem": over an arbitrary unique factorization domain and
-- its fraction field, every root of a monic polynomial lies in the image of
-- the domain's canonical embedding. This file contains no proof.

{-# OPTIONS --safe #-}

module Q180345X_integral_root_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not P =
  P -> Bottom

_≠_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x ≠ y =
  Not (x ≡ y)

record _and_
  {a b : Level}
  (P : Set a)
  (Q : Set b) :
  Set (a ⊔ b) where

  constructor conjunction
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

data All
  {a p : Level}
  {A : Set a}
  (P : A -> Set p) :
  List A ->
  Set (a ⊔ p) where

  all-empty :
    All P []

  all-cons :
    {x : A} ->
    {xs : List A} ->
    P x ->
    All P xs ->
    All P (x ∷ xs)

record CommutativeRing
  {a : Level}
  (A : Set a) :
  Set a where

  field
    zeroR oneR : A
    addR multiplyR : A -> A -> A
    negateR : A -> A

    add-commutative :
      (x y : A) ->
      addR x y ≡ addR y x
    add-associative :
      (x y z : A) ->
      addR (addR x y) z ≡ addR x (addR y z)
    add-zero :
      (x : A) ->
      addR x zeroR ≡ x
    add-inverse :
      (x : A) ->
      addR x (negateR x) ≡ zeroR

    multiply-commutative :
      (x y : A) ->
      multiplyR x y ≡ multiplyR y x
    multiply-associative :
      (x y z : A) ->
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-one :
      (x : A) ->
      multiplyR x oneR ≡ x
    distribute :
      (x y z : A) ->
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)

record IntegralDomain
  {a : Level}
  (A : Set a) :
  Set a where

  field
    ring : CommutativeRing A
    one-not-zero :
      CommutativeRing.oneR ring ≠
      CommutativeRing.zeroR ring
    no-zero-divisors :
      (x y : A) ->
      CommutativeRing.multiplyR ring x y ≡
      CommutativeRing.zeroR ring ->
      (x ≡ CommutativeRing.zeroR ring) or
      (y ≡ CommutativeRing.zeroR ring)

record Field
  {a : Level}
  (K : Set a) :
  Set a where

  field
    ring : CommutativeRing K
    inverseF : K -> K
    one-not-zero :
      CommutativeRing.oneR ring ≠
      CommutativeRing.zeroR ring
    multiply-inverse :
      (x : K) ->
      x ≠ CommutativeRing.zeroR ring ->
      CommutativeRing.multiplyR ring x (inverseF x) ≡
      CommutativeRing.oneR ring

record RingHom
  {a b : Level}
  {A : Set a}
  {B : Set b}
  (domain : CommutativeRing A)
  (codomain : CommutativeRing B) :
  Set (a ⊔ b) where

  field
    map : A -> B
    map-zero :
      map (CommutativeRing.zeroR domain) ≡
      CommutativeRing.zeroR codomain
    map-one :
      map (CommutativeRing.oneR domain) ≡
      CommutativeRing.oneR codomain
    map-add :
      (x y : A) ->
      map (CommutativeRing.addR domain x y) ≡
      CommutativeRing.addR codomain (map x) (map y)
    map-multiply :
      (x y : A) ->
      map (CommutativeRing.multiplyR domain x y) ≡
      CommutativeRing.multiplyR codomain (map x) (map y)

Divides :
  {a : Level} ->
  {A : Set a} ->
  CommutativeRing A ->
  A ->
  A ->
  Set a
Divides ring divisor dividend =
  Σ _
    (λ quotient ->
      dividend ≡
      CommutativeRing.multiplyR ring divisor quotient)

Unit :
  {a : Level} ->
  {A : Set a} ->
  CommutativeRing A ->
  A ->
  Set a
Unit ring x =
  Σ _
    (λ inverse ->
      CommutativeRing.multiplyR ring x inverse ≡
      CommutativeRing.oneR ring)

Associated :
  {a : Level} ->
  {A : Set a} ->
  CommutativeRing A ->
  A ->
  A ->
  Set a
Associated ring x y =
  Σ _
    (λ unit-factor ->
      Unit ring unit-factor and
      (x ≡ CommutativeRing.multiplyR ring unit-factor y))

record Irreducible
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A)
  (p : A) :
  Set a where

  field
    nonzero :
      p ≠ CommutativeRing.zeroR ring
    nonunit :
      Not (Unit ring p)
    factor-is-trivial :
      (x y : A) ->
      p ≡ CommutativeRing.multiplyR ring x y ->
      Unit ring x or Unit ring y

record Prime
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A)
  (p : A) :
  Set a where

  field
    nonzero :
      p ≠ CommutativeRing.zeroR ring
    nonunit :
      Not (Unit ring p)
    divides-product :
      (x y : A) ->
      Divides ring p (CommutativeRing.multiplyR ring x y) ->
      Divides ring p x or Divides ring p y

product :
  {a : Level} ->
  {A : Set a} ->
  (ring : CommutativeRing A) ->
  List A ->
  A
product ring [] =
  CommutativeRing.oneR ring
product ring (x ∷ xs) =
  CommutativeRing.multiplyR ring x (product ring xs)

record UniqueFactorizationMonoid
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A) :
  Set a where

  field
    factorization :
      (x : A) ->
      x ≠ CommutativeRing.zeroR ring ->
      Σ (List A)
        (λ factors ->
          All (Irreducible ring) factors and
          Associated ring x (product ring factors))
    irreducible-is-prime :
      (p : A) ->
      Irreducible ring p ->
      Prime ring p

record FractionField
  {a k : Level}
  {A : Set a}
  {K : Set k}
  (domain : IntegralDomain A)
  (field-structure : Field K)
  (algebra-map :
    RingHom
      (IntegralDomain.ring domain)
      (Field.ring field-structure)) :
  Set (a ⊔ k) where

  private
    base = IntegralDomain.ring domain
    extension = Field.ring field-structure

  field
    map-injective :
      (x y : A) ->
      RingHom.map algebra-map x ≡ RingHom.map algebra-map y ->
      x ≡ y
    every-element-is-fraction :
      (r : K) ->
      Σ A
        (λ numerator ->
          Σ A
            (λ denominator ->
              denominator ≠ CommutativeRing.zeroR base and
              (RingHom.map algebra-map numerator ≡
                CommutativeRing.multiplyR extension r
                  (RingHom.map algebra-map denominator))))

data DegreeCorrect
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A)
  (coefficient : Nat -> A) :
  Nat ->
  Set a where

  zero-polynomial :
    ((n : Nat) ->
      coefficient n ≡ CommutativeRing.zeroR ring) ->
    DegreeCorrect ring coefficient zero

  nonzero-polynomial :
    {degree : Nat} ->
    coefficient degree ≠ CommutativeRing.zeroR ring ->
    ((offset : Nat) ->
      coefficient (degree + suc offset) ≡
      CommutativeRing.zeroR ring) ->
    DegreeCorrect ring coefficient degree

record Polynomial
  {a : Level}
  {A : Set a}
  (ring : CommutativeRing A) :
  Set a where

  field
    coefficient : Nat -> A
    degree : Nat
    degree-correct :
      DegreeCorrect ring coefficient degree

leadingCoefficient :
  {a : Level} ->
  {A : Set a} ->
  {ring : CommutativeRing A} ->
  Polynomial ring ->
  A
leadingCoefficient polynomial =
  Polynomial.coefficient polynomial (Polynomial.degree polynomial)

evaluateFrom :
  {a k : Level} ->
  {A : Set a} ->
  {K : Set k} ->
  {base : CommutativeRing A} ->
  {extension : CommutativeRing K} ->
  RingHom base extension ->
  Polynomial base ->
  K ->
  Nat ->
  Nat ->
  K
evaluateFrom {extension = extension}
  algebra-map polynomial root start zero =
  RingHom.map algebra-map
    (Polynomial.coefficient polynomial start)
evaluateFrom {extension = extension}
  algebra-map polynomial root start (suc count) =
  CommutativeRing.addR extension
    (RingHom.map algebra-map
      (Polynomial.coefficient polynomial start))
    (CommutativeRing.multiplyR extension root
      (evaluateFrom algebra-map polynomial root (suc start) count))

evaluate :
  {a k : Level} ->
  {A : Set a} ->
  {K : Set k} ->
  {base : CommutativeRing A} ->
  {extension : CommutativeRing K} ->
  RingHom base extension ->
  Polynomial base ->
  K ->
  K
evaluate algebra-map polynomial root =
  evaluateFrom algebra-map polynomial root zero
    (Polynomial.degree polynomial)

Monic :
  {a : Level} ->
  {A : Set a} ->
  (ring : CommutativeRing A) ->
  Polynomial ring ->
  Set a
Monic ring polynomial =
  leadingCoefficient polynomial ≡
  CommutativeRing.oneR ring

IsRoot :
  {a k : Level} ->
  {A : Set a} ->
  {K : Set k} ->
  {base : CommutativeRing A} ->
  {extension : CommutativeRing K} ->
  RingHom base extension ->
  Polynomial base ->
  K ->
  Set k
IsRoot {extension = extension} algebra-map polynomial root =
  evaluate algebra-map polynomial root ≡
  CommutativeRing.zeroR extension

IsInteger :
  {a k : Level} ->
  {A : Set a} ->
  {K : Set k} ->
  {base : CommutativeRing A} ->
  {extension : CommutativeRing K} ->
  RingHom base extension ->
  K ->
  Set (a ⊔ k)
IsInteger {A = A} algebra-map root =
  Σ A
    (λ integer ->
      RingHom.map algebra-map integer ≡ root)

isInteger-of-is-root-of-monic :
  (a k : Level) ->
  Set (lsuc (a ⊔ k))
isInteger-of-is-root-of-monic a k =
  (A : Set a) ->
  (K : Set k) ->
  (domain : IntegralDomain A) ->
  (ufd :
    UniqueFactorizationMonoid
      (IntegralDomain.ring domain)) ->
  (field-structure : Field K) ->
  (algebra-map :
    RingHom
      (IntegralDomain.ring domain)
      (Field.ring field-structure)) ->
  FractionField domain field-structure algebra-map ->
  (polynomial :
    Polynomial (IntegralDomain.ring domain)) ->
  Monic (IntegralDomain.ring domain) polynomial ->
  (root : K) ->
  IsRoot algebra-map polynomial root ->
  IsInteger algebra-map root
