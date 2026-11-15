-- Statement-only formalization of thousand-theorems corpus artifact Q1144897,
-- "Brouwer fixed-point theorem": every continuous self-map of a nonempty
-- compact convex subset of a finite-dimensional real normed vector space has
-- a fixed point. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1144897_brouwer_fixed_point_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 3 _×_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

_≠_ :
  {a : Level} →
  {A : Set a} →
  A →
  A →
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

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → Either A B
  right : B → Either A B

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A →
  Set a where

  at-head :
    {xs : List A} →
    Member x (x ∷ xs)

  in-tail :
    {y : A} →
    {xs : List A} →
    Member x xs →
    Member x (y ∷ xs)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

-- A complete Archimedean ordered field is a presentation of the real line.
record RealLine
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR :
      R

    addR multiplyR :
      R →
      R →
      R

    negateR reciprocalR absoluteR :
      R →
      R

    lessOrEqualR :
      R →
      R →
      Set r

    fromNatR :
      Nat →
      R

    one-not-zeroR :
      oneR ≠ zeroR

    add-commutativeR :
      (x y : R) →
      addR x y ≡ addR y x

    add-associativeR :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)

    add-zeroR :
      (x : R) →
      addR x zeroR ≡ x

    add-inverseR :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-commutativeR :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x

    multiply-associativeR :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡ multiplyR x (multiplyR y z)

    multiply-oneR :
      (x : R) →
      multiplyR x oneR ≡ x

    multiply-zeroR :
      (x : R) →
      multiplyR x zeroR ≡ zeroR

    distributeR :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)

    multiply-reciprocalR :
      (x : R) →
      x ≠ zeroR →
      multiplyR x (reciprocalR x) ≡ oneR

    order-reflexiveR :
      (x : R) →
      lessOrEqualR x x

    order-transitiveR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR y z →
      lessOrEqualR x z

    order-antisymmetricR :
      (x y : R) →
      lessOrEqualR x y →
      lessOrEqualR y x →
      x ≡ y

    order-totalR :
      (x y : R) →
      Either (lessOrEqualR x y) (lessOrEqualR y x)

    add-orderR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)

    multiply-nonnegativeR :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)

    zero-less-than-oneR :
      lessOrEqualR zeroR oneR × zeroR ≠ oneR

    absolute-nonnegativeR :
      (x : R) →
      lessOrEqualR zeroR (absoluteR x)

    absolute-of-nonnegativeR :
      (x : R) →
      lessOrEqualR zeroR x →
      absoluteR x ≡ x

    absolute-of-nonpositiveR :
      (x : R) →
      lessOrEqualR x zeroR →
      absoluteR x ≡ negateR x

    fromNat-zeroR :
      fromNatR zero ≡ zeroR

    fromNat-successorR :
      (n : Nat) →
      fromNatR (suc n) ≡ addR (fromNatR n) oneR

    fromNat-injectiveR :
      (m n : Nat) →
      fromNatR m ≡ fromNatR n →
      m ≡ n

    archimedeanR :
      (x : R) →
      Σ Nat (λ n → lessOrEqualR x (fromNatR n))

    least-upper-boundR :
      (P : R → Set r) →
      Σ R P →
      Σ R (λ upper → (x : R) → P x → lessOrEqualR x upper) →
      Σ R
        (λ supremum →
          ((x : R) → P x → lessOrEqualR x supremum)
          ×
          ((upper : R) →
            ((x : R) → P x → lessOrEqualR x upper) →
            lessOrEqualR supremum upper))

open RealLine

StrictLessR :
  {r : Level} →
  {R : Set r} →
  RealLine R →
  R →
  R →
  Set r
StrictLessR reals x y =
  lessOrEqualR reals x y × x ≠ y

record RealVectorSpace
  {r v : Level}
  {R : Set r}
  (reals : RealLine R)
  (V : Set v) :
  Set (lsuc (r ⊔ v)) where

  field
    zeroV :
      V

    addV :
      V →
      V →
      V

    negateV :
      V →
      V

    scaleV :
      R →
      V →
      V

    add-commutativeV :
      (x y : V) →
      addV x y ≡ addV y x

    add-associativeV :
      (x y z : V) →
      addV (addV x y) z ≡ addV x (addV y z)

    add-zeroV :
      (x : V) →
      addV x zeroV ≡ x

    add-inverseV :
      (x : V) →
      addV x (negateV x) ≡ zeroV

    scale-oneV :
      (x : V) →
      scaleV (oneR reals) x ≡ x

    scale-associativeV :
      (a b : R) →
      (x : V) →
      scaleV (multiplyR reals a b) x ≡ scaleV a (scaleV b x)

    scale-add-vectorsV :
      (a : R) →
      (x y : V) →
      scaleV a (addV x y) ≡ addV (scaleV a x) (scaleV a y)

    scale-add-scalarsV :
      (a b : R) →
      (x : V) →
      scaleV (addR reals a b) x ≡ addV (scaleV a x) (scaleV b x)

    scale-zero-vectorV :
      (a : R) →
      scaleV a zeroV ≡ zeroV

    scale-zero-scalarV :
      (x : V) →
      scaleV (zeroR reals) x ≡ zeroV

open RealVectorSpace

subtractV :
  {r v : Level} →
  {R : Set r} →
  {V : Set v} →
  {reals : RealLine R} →
  RealVectorSpace reals V →
  V →
  V →
  V
subtractV space x y =
  addV space x (negateV space y)

record NormedSpace
  {r v : Level}
  {R : Set r}
  {V : Set v}
  (reals : RealLine R)
  (space : RealVectorSpace reals V) :
  Set (lsuc (r ⊔ v)) where

  field
    normV :
      V →
      R

    norm-nonnegativeV :
      (x : V) →
      lessOrEqualR reals (zeroR reals) (normV x)

    norm-zeroV :
      normV (zeroV space) ≡ zeroR reals

    norm-zero-onlyV :
      (x : V) →
      normV x ≡ zeroR reals →
      x ≡ zeroV space

    norm-triangleV :
      (x y : V) →
      lessOrEqualR reals
        (normV (addV space x y))
        (addR reals (normV x) (normV y))

    norm-scaleV :
      (a : R) →
      (x : V) →
      normV (scaleV space a x) ≡
      multiplyR reals (absoluteR reals a) (normV x)

open NormedSpace

Distance :
  {r v : Level} →
  {R : Set r} →
  {V : Set v} →
  {reals : RealLine R} →
  {space : RealVectorSpace reals V} →
  NormedSpace reals space →
  V →
  V →
  R
Distance {space = space} normed x y =
  normV normed (subtractV space x y)

sumScaled :
  {r v : Level} →
  {R : Set r} →
  {V : Set v} →
  {reals : RealLine R} →
  (space : RealVectorSpace reals V) →
  {n : Nat} →
  (Fin n → R) →
  (Fin n → V) →
  V
sumScaled space {zero} coefficients vectors =
  zeroV space
sumScaled space {suc n} coefficients vectors =
  addV space
    (scaleV space (coefficients fzero) (vectors fzero))
    (sumScaled space
      (λ i → coefficients (fsuc i))
      (λ i → vectors (fsuc i)))

record FiniteDimensional
  {r v : Level}
  {R : Set r}
  {V : Set v}
  (reals : RealLine R)
  (space : RealVectorSpace reals V) :
  Set (lsuc (r ⊔ v)) where

  field
    dimension :
      Nat

    basis :
      Fin dimension →
      V

    basis-independent :
      (coefficients : Fin dimension → R) →
      sumScaled space coefficients basis ≡ zeroV space →
      (i : Fin dimension) →
      coefficients i ≡ zeroR reals

    basis-spans :
      (x : V) →
      Σ (Fin dimension → R)
        (λ coefficients →
          sumScaled space coefficients basis ≡ x)

Subset :
  {v : Level} →
  Set v →
  Set (lsuc v)
Subset {v} V =
  V → Set v

Nonempty :
  {v : Level} →
  {V : Set v} →
  Subset V →
  Set v
Nonempty {V = V} subset =
  Σ V subset

Convex :
  {r v : Level} →
  {R : Set r} →
  {V : Set v} →
  (reals : RealLine R) →
  RealVectorSpace reals V →
  Subset V →
  Set (r ⊔ v)
Convex {R = R} {V = V} reals space subset =
  (a b : R) →
  lessOrEqualR reals (zeroR reals) a →
  lessOrEqualR reals (zeroR reals) b →
  addR reals a b ≡ oneR reals →
  (x y : V) →
  subset x →
  subset y →
  subset
    (addV space
      (scaleV space a x)
      (scaleV space b y))

IsOpen :
  {r v : Level} →
  {R : Set r} →
  {V : Set v} →
  {reals : RealLine R} →
  {space : RealVectorSpace reals V} →
  NormedSpace reals space →
  Subset V →
  Set (r ⊔ v)
IsOpen {R = R} {V = V} {reals = reals} normed subset =
  (center : V) →
  subset center →
  Σ R
    (λ radius →
      StrictLessR reals (zeroR reals) radius
      ×
      ((point : V) →
        StrictLessR reals (Distance normed center point) radius →
        subset point))

Covers :
  {i v : Level} →
  {I : Set i} →
  {V : Set v} →
  Subset V →
  (I → Subset V) →
  Set (i ⊔ v)
Covers {I = I} {V = V} subset family =
  (x : V) →
  subset x →
  Σ I (λ index → family index x)

FiniteSubcover :
  {i v : Level} →
  {I : Set i} →
  {V : Set v} →
  Subset V →
  (I → Subset V) →
  Set (i ⊔ v)
FiniteSubcover {I = I} {V = V} subset family =
  Σ (List I)
    (λ selected →
      (x : V) →
      subset x →
      Σ I
        (λ index →
          Member index selected × family index x))

Compact :
  {r v : Level} →
  {R : Set r} →
  {V : Set v} →
  {reals : RealLine R} →
  {space : RealVectorSpace reals V} →
  NormedSpace reals space →
  Subset V →
  Setω
Compact {r = r} {v = v} {V = V} normed subset =
  (i : Level) →
  (I : Set i) →
  (family : I → Subset V) →
  ((index : I) → IsOpen normed (family index)) →
  Covers subset family →
  FiniteSubcover subset family

record PointIn
  {v : Level}
  {V : Set v}
  (subset : Subset V) :
  Set v where

  constructor point-in
  field
    point :
      V

    point-membership :
      subset point

open PointIn

ContinuousOnSubset :
  {r v : Level} →
  {R : Set r} →
  {V : Set v} →
  {reals : RealLine R} →
  {space : RealVectorSpace reals V} →
  (normed : NormedSpace reals space) →
  (subset : Subset V) →
  (PointIn subset → PointIn subset) →
  Set (r ⊔ v)
ContinuousOnSubset {R = R} {reals = reals} normed subset function =
  (x : PointIn subset) →
  (epsilon : R) →
  StrictLessR reals (zeroR reals) epsilon →
  Σ R
    (λ delta →
      StrictLessR reals (zeroR reals) delta
      ×
      ((y : PointIn subset) →
        StrictLessR reals
          (Distance normed (point x) (point y))
          delta →
        StrictLessR reals
          (Distance normed (point (function x)) (point (function y)))
          epsilon))

record ContinuousSelfMap
  {r v : Level}
  {R : Set r}
  {V : Set v}
  {reals : RealLine R}
  {space : RealVectorSpace reals V}
  (normed : NormedSpace reals space)
  (subset : Subset V) :
  Set (lsuc (r ⊔ v)) where

  field
    apply :
      PointIn subset →
      PointIn subset

    continuous :
      ContinuousOnSubset normed subset apply

open ContinuousSelfMap

brouwer-fixed-point-theorem : Setω
brouwer-fixed-point-theorem =
  {r v : Level} →
  (R : Set r) →
  (reals : RealLine R) →
  (V : Set v) →
  (space : RealVectorSpace reals V) →
  (normed : NormedSpace reals space) →
  FiniteDimensional reals space →
  (subset : Subset V) →
  Convex reals space subset →
  Compact normed subset →
  Nonempty subset →
  (function : ContinuousSelfMap normed subset) →
  Σ (PointIn subset)
    (λ x →
      point (apply function x) ≡ point x)
