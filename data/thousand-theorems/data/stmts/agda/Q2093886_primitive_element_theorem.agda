-- Statement-only formalization of thousand-theorems corpus artifact Q2093886,
-- "Primitive element theorem": every finite-dimensional separable field
-- extension is generated over its base field by one element. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q2093886PrimitiveElementTheorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 2 _×_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_≠_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x ≠ y =
  Not (x ≡ y)

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

record Field
  {a : Level}
  (A : Set a) :
  Set a where

  field
    ring : CommutativeRing A
    inverseF : A -> A
    one-not-zero :
      CommutativeRing.oneR ring ≠
      CommutativeRing.zeroR ring
    inverse-zero :
      inverseF (CommutativeRing.zeroR ring) ≡
      CommutativeRing.zeroR ring
    multiply-inverse :
      (x : A) ->
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

sumFin :
  {a : Level} ->
  {A : Set a} ->
  CommutativeRing A ->
  (n : Nat) ->
  (Fin n -> A) ->
  A
sumFin ring zero values =
  CommutativeRing.zeroR ring
sumFin ring (suc n) values =
  CommutativeRing.addR ring
    (values fzero)
    (sumFin ring n (λ i -> values (fsuc i)))

linearCombination :
  {f e : Level} ->
  {F : Set f} ->
  {E : Set e} ->
  (base : CommutativeRing F) ->
  (extension : CommutativeRing E) ->
  RingHom base extension ->
  (n : Nat) ->
  (Fin n -> E) ->
  (Fin n -> F) ->
  E
linearCombination base extension algebra-map n vectors coefficients =
  sumFin extension n
    (λ i ->
      CommutativeRing.multiplyR extension
        (RingHom.map algebra-map (coefficients i))
        (vectors i))

record HasBasis
  {f e : Level}
  {F : Set f}
  {E : Set e}
  (base : CommutativeRing F)
  (extension : CommutativeRing E)
  (algebra-map : RingHom base extension)
  (dimension : Nat) :
  Set (f ⊔ e) where

  field
    basis : Fin dimension -> E
    linearly-independent :
      (coefficients : Fin dimension -> F) ->
      linearCombination
        base extension algebra-map dimension basis coefficients
      ≡
      CommutativeRing.zeroR extension ->
      (i : Fin dimension) ->
      coefficients i ≡ CommutativeRing.zeroR base
    spans :
      (x : E) ->
      Σ (Fin dimension -> F)
        (λ coefficients ->
          linearCombination
            base extension algebra-map dimension basis coefficients
          ≡
          x)

FiniteDimensional :
  {f e : Level} ->
  {F : Set f} ->
  {E : Set e} ->
  (base : CommutativeRing F) ->
  (extension : CommutativeRing E) ->
  RingHom base extension ->
  Set (f ⊔ e)
FiniteDimensional base extension algebra-map =
  Σ Nat
    (λ dimension ->
      HasBasis base extension algebra-map dimension)

record Polynomial
  {f : Level}
  (F : Set f)
  (field-structure : Field F) :
  Set f where

  private
    ring = Field.ring field-structure

  field
    coefficient : Nat -> F
    bound : Nat
    zero-after-bound :
      (offset : Nat) ->
      coefficient (bound + suc offset) ≡
      CommutativeRing.zeroR ring

evaluateFrom :
  {a : Level} ->
  {A : Set a} ->
  CommutativeRing A ->
  (Nat -> A) ->
  A ->
  Nat ->
  Nat ->
  A
evaluateFrom ring coefficient x start zero =
  coefficient start
evaluateFrom ring coefficient x start (suc count) =
  CommutativeRing.addR ring
    (coefficient start)
    (CommutativeRing.multiplyR ring x
      (evaluateFrom ring coefficient x (suc start) count))

evaluate :
  {f e : Level} ->
  {F : Set f} ->
  {E : Set e} ->
  (base-field : Field F) ->
  (extension-field : Field E) ->
  RingHom
    (Field.ring base-field)
    (Field.ring extension-field) ->
  Polynomial F base-field ->
  E ->
  E
evaluate base-field extension-field algebra-map polynomial x =
  evaluateFrom
    (Field.ring extension-field)
    (λ n ->
      RingHom.map algebra-map
        (Polynomial.coefficient polynomial n))
    x
    zero
    (Polynomial.bound polynomial)

natScale :
  {a : Level} ->
  {A : Set a} ->
  CommutativeRing A ->
  Nat ->
  A ->
  A
natScale ring zero x =
  CommutativeRing.zeroR ring
natScale ring (suc n) x =
  CommutativeRing.addR ring x (natScale ring n x)

derivativeCoefficient :
  {f : Level} ->
  {F : Set f} ->
  {field-structure : Field F} ->
  Polynomial F field-structure ->
  Nat ->
  F
derivativeCoefficient {field-structure = field-structure} polynomial n =
  natScale
    (Field.ring field-structure)
    (suc n)
    (Polynomial.coefficient polynomial (suc n))

multiplyCoefficient :
  {a : Level} ->
  {A : Set a} ->
  CommutativeRing A ->
  (Nat -> A) ->
  (Nat -> A) ->
  Nat ->
  A
multiplyCoefficient ring left right zero =
  CommutativeRing.multiplyR ring (left zero) (right zero)
multiplyCoefficient ring left right (suc n) =
  CommutativeRing.addR ring
    (CommutativeRing.multiplyR ring (left zero) (right (suc n)))
    (multiplyCoefficient ring (λ i -> left (suc i)) right n)

unitCoefficient :
  {a : Level} ->
  {A : Set a} ->
  CommutativeRing A ->
  Nat ->
  A
unitCoefficient ring zero =
  CommutativeRing.oneR ring
unitCoefficient ring (suc n) =
  CommutativeRing.zeroR ring

NonzeroPolynomial :
  {f : Level} ->
  {F : Set f} ->
  {field-structure : Field F} ->
  Polynomial F field-structure ->
  Set f
NonzeroPolynomial {field-structure = field-structure} polynomial =
  Σ Nat
    (λ n ->
      Polynomial.coefficient polynomial n ≠
      CommutativeRing.zeroR (Field.ring field-structure))

CoprimeWithDerivative :
  {f : Level} ->
  {F : Set f} ->
  {field-structure : Field F} ->
  Polynomial F field-structure ->
  Set f
CoprimeWithDerivative
  {field-structure = field-structure}
  polynomial =
  Σ (Polynomial _ field-structure)
    (λ left ->
      Σ (Polynomial _ field-structure)
        (λ right ->
          (n : Nat) ->
          CommutativeRing.addR ring
            (multiplyCoefficient ring
              (Polynomial.coefficient left)
              (Polynomial.coefficient polynomial)
              n)
            (multiplyCoefficient ring
              (Polynomial.coefficient right)
              (derivativeCoefficient polynomial)
              n)
          ≡
          unitCoefficient ring n))
  where
  ring = Field.ring field-structure

SeparableElement :
  {f e : Level} ->
  {F : Set f} ->
  {E : Set e} ->
  (base-field : Field F) ->
  (extension-field : Field E) ->
  RingHom
    (Field.ring base-field)
    (Field.ring extension-field) ->
  E ->
  Set (f ⊔ e)
SeparableElement base-field extension-field algebra-map x =
  Σ (Polynomial _ base-field)
    (λ polynomial ->
      NonzeroPolynomial polynomial
      ×
      ((evaluate
          base-field
          extension-field
          algebra-map
          polynomial
          x
        ≡
        CommutativeRing.zeroR (Field.ring extension-field))
       ×
       CoprimeWithDerivative polynomial))

record Subfield
  {e : Level}
  {E : Set e}
  (field-structure : Field E) :
  Set (lsuc e) where

  private
    ring = Field.ring field-structure

  field
    member : E -> Set e
    contains-zero :
      member (CommutativeRing.zeroR ring)
    contains-one :
      member (CommutativeRing.oneR ring)
    closed-under-addition :
      (x y : E) ->
      member x ->
      member y ->
      member (CommutativeRing.addR ring x y)
    closed-under-negation :
      (x : E) ->
      member x ->
      member (CommutativeRing.negateR ring x)
    closed-under-multiplication :
      (x y : E) ->
      member x ->
      member y ->
      member (CommutativeRing.multiplyR ring x y)
    closed-under-inverse :
      (x : E) ->
      member x ->
      member (Field.inverseF field-structure x)

GeneratedBy :
  {f e : Level} ->
  {F : Set f} ->
  {E : Set e} ->
  (base-field : Field F) ->
  (extension-field : Field E) ->
  (algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)) ->
  E ->
  E ->
  Set (f ⊔ lsuc e)
GeneratedBy base-field extension-field algebra-map generator x =
  (subfield : Subfield extension-field) ->
  ((a : _) ->
    Subfield.member subfield (RingHom.map algebra-map a)) ->
  Subfield.member subfield generator ->
  Subfield.member subfield x

the-primitive-element-theorem : Setω
the-primitive-element-theorem =
  ∀ {f e : Level} ->
  (F : Set f) ->
  (E : Set e) ->
  (base-field : Field F) ->
  (extension-field : Field E) ->
  (algebra-map :
    RingHom
      (Field.ring base-field)
      (Field.ring extension-field)) ->
  FiniteDimensional
    (Field.ring base-field)
    (Field.ring extension-field)
    algebra-map ->
  ((x : E) ->
    SeparableElement
      base-field
      extension-field
      algebra-map
      x) ->
  Σ E
    (λ generator ->
      (x : E) ->
      GeneratedBy
        base-field
        extension-field
        algebra-map
        generator
        x)
