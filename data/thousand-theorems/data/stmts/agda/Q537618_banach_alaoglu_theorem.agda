-- Statement-only formalization of thousand-theorems corpus artifact Q537618,
-- "Banach–Alaoglu theorem": the polar of a neighborhood of zero in a
-- seminormed space over a proper nontrivially normed field is compact in the
-- weak-star topology on the continuous dual. This file contains no proof.

{-# OPTIONS --safe #-}

module Q537618_banach_alaoglu_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat) renaming (zero to zeroN; suc to sucN)

infix 4 _≠_
infixr 3 _×_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

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

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

record Top {a : Level} : Set a where
  constructor top

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A ->
  Set a where

  at-head :
    {xs : List A} ->
    Member x (x ∷ xs)

  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

All :
  {a b : Level} ->
  {A : Set a} ->
  (A -> Set b) ->
  List A ->
  Set (a ⊔ b)
All P [] =
  Top
All P (x ∷ xs) =
  P x × All P xs

Subset :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Subset {a} X =
  X -> Set a

Family :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Family {a} X =
  Subset X -> Set a

SubsetOf :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Subset X ->
  Set a
SubsetOf {X = X} U V =
  (x : X) ->
  U x ->
  V x

Covers :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Family X ->
  Set (lsuc a)
Covers {X = X} U cover =
  (x : X) ->
  U x ->
  Exists (Subset X)
    (\ V ->
      cover V × V x)

FiniteSubcover :
  {a : Level} ->
  {X : Set a} ->
  Subset X ->
  Family X ->
  Set (lsuc a)
FiniteSubcover {X = X} U cover =
  Exists (List (Subset X))
    (\ selected ->
      ((V : Subset X) ->
        Member V selected ->
        cover V)
      ×
      ((x : X) ->
        U x ->
        Exists (Subset X)
          (\ V ->
            Member V selected × V x)))

CompactFor :
  {a : Level} ->
  {X : Set a} ->
  (Subset X -> Set a) ->
  Subset X ->
  Set (lsuc a)
CompactFor {X = X} Open U =
  (cover : Family X) ->
  ((V : Subset X) ->
    cover V ->
    Open V) ->
  Covers U cover ->
  FiniteSubcover U cover

-- A complete Archimedean ordered field is a presentation of the real line.
record RealLine
  {a : Level}
  (R : Set a) :
  Set (lsuc a) where

  field
    zeroR oneR :
      R

    addR multiplyR :
      R ->
      R ->
      R

    negateR reciprocalR :
      R ->
      R

    lessOrEqualR :
      R ->
      R ->
      Set a

    fromNatR :
      Nat ->
      R

    one-not-zeroR :
      oneR ≠ zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y ≡ addR y x

    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z ≡ addR x (addR y z)

    add-zeroR :
      (x : R) ->
      addR x zeroR ≡ x

    add-inverseR :
      (x : R) ->
      addR x (negateR x) ≡ zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y ≡ multiplyR y x

    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ≡ multiplyR x (multiplyR y z)

    multiply-oneR :
      (x : R) ->
      multiplyR x oneR ≡ x

    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR ≡ zeroR

    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)

    reciprocal-zeroR :
      reciprocalR zeroR ≡ zeroR

    multiply-reciprocalR :
      (x : R) ->
      x ≠ zeroR ->
      multiplyR x (reciprocalR x) ≡ oneR

    order-reflexiveR :
      (x : R) ->
      lessOrEqualR x x

    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z

    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x ≡ y

    order-totalR :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)

    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)

    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)

    zero-less-than-oneR :
      lessOrEqualR zeroR oneR × zeroR ≠ oneR

    fromNat-zeroR :
      fromNatR zeroN ≡ zeroR

    fromNat-successorR :
      (n : Nat) ->
      fromNatR (sucN n) ≡ addR (fromNatR n) oneR

    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m ≡ fromNatR n ->
      m ≡ n

    archimedeanR :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqualR x (fromNatR n))

    least-upper-boundR :
      (P : R -> Set a) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqualR x supremum)
          ×
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open RealLine

StrictLess :
  {a : Level} ->
  {R : Set a} ->
  RealLine R ->
  R ->
  R ->
  Set a
StrictLess reals x y =
  lessOrEqualR reals x y × x ≠ y

Positive :
  {a : Level} ->
  {R : Set a} ->
  RealLine R ->
  R ->
  Set a
Positive reals x =
  StrictLess reals (zeroR reals) x

record NontriviallyNormedField
  {a : Level}
  (R K : Set a)
  (reals : RealLine R) :
  Set a where

  field
    zeroK oneK :
      K

    addK multiplyK :
      K ->
      K ->
      K

    negateK reciprocalK :
      K ->
      K

    normK :
      K ->
      R

    one-not-zeroK :
      oneK ≠ zeroK

    add-commutativeK :
      (x y : K) ->
      addK x y ≡ addK y x

    add-associativeK :
      (x y z : K) ->
      addK (addK x y) z ≡ addK x (addK y z)

    add-zeroK :
      (x : K) ->
      addK x zeroK ≡ x

    add-inverseK :
      (x : K) ->
      addK x (negateK x) ≡ zeroK

    multiply-commutativeK :
      (x y : K) ->
      multiplyK x y ≡ multiplyK y x

    multiply-associativeK :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ≡ multiplyK x (multiplyK y z)

    multiply-oneK :
      (x : K) ->
      multiplyK x oneK ≡ x

    multiply-zeroK :
      (x : K) ->
      multiplyK x zeroK ≡ zeroK

    distributeK :
      (x y z : K) ->
      multiplyK x (addK y z) ≡
      addK (multiplyK x y) (multiplyK x z)

    reciprocal-zeroK :
      reciprocalK zeroK ≡ zeroK

    multiply-reciprocalK :
      (x : K) ->
      x ≠ zeroK ->
      multiplyK x (reciprocalK x) ≡ oneK

    norm-nonnegativeK :
      (x : K) ->
      lessOrEqualR reals (zeroR reals) (normK x)

    norm-zeroK :
      normK zeroK ≡ zeroR reals

    norm-zero-onlyK :
      (x : K) ->
      normK x ≡ zeroR reals ->
      x ≡ zeroK

    norm-negateK :
      (x : K) ->
      normK (negateK x) ≡ normK x

    norm-addK :
      (x y : K) ->
      lessOrEqualR reals
        (normK (addK x y))
        (addR reals (normK x) (normK y))

    norm-multiplyK :
      (x y : K) ->
      normK (multiplyK x y) ≡
      multiplyR reals (normK x) (normK y)

    norm-nontrivialK :
      Exists K
        (\ x ->
          StrictLess reals (oneR reals) (normK x))

open NontriviallyNormedField

record SeminormedSpace
  {a : Level}
  (R K E : Set a)
  (reals : RealLine R)
  (scalars : NontriviallyNormedField R K reals) :
  Set a where

  field
    zeroE :
      E

    addE :
      E ->
      E ->
      E

    negateE :
      E ->
      E

    scaleE :
      K ->
      E ->
      E

    normE :
      E ->
      R

    add-commutativeE :
      (x y : E) ->
      addE x y ≡ addE y x

    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z ≡ addE x (addE y z)

    add-zeroE :
      (x : E) ->
      addE x zeroE ≡ x

    add-inverseE :
      (x : E) ->
      addE x (negateE x) ≡ zeroE

    scale-oneE :
      (x : E) ->
      scaleE (oneK scalars) x ≡ x

    scale-associativeE :
      (a b : K) ->
      (x : E) ->
      scaleE (multiplyK scalars a b) x ≡ scaleE a (scaleE b x)

    scale-add-vectorsE :
      (a : K) ->
      (x y : E) ->
      scaleE a (addE x y) ≡ addE (scaleE a x) (scaleE a y)

    scale-add-scalarsE :
      (a b : K) ->
      (x : E) ->
      scaleE (addK scalars a b) x ≡ addE (scaleE a x) (scaleE b x)

    norm-nonnegativeE :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (normE x)

    norm-zeroE :
      normE zeroE ≡ zeroR reals

    norm-negateE :
      (x : E) ->
      normE (negateE x) ≡ normE x

    norm-addE :
      (x y : E) ->
      lessOrEqualR reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))

    norm-scaleE :
      (a : K) ->
      (x : E) ->
      normE (scaleE a x) ≡
      multiplyR reals (normK scalars a) (normE x)

open SeminormedSpace

subtractK :
  {a : Level} ->
  {R K : Set a} ->
  {reals : RealLine R} ->
  NontriviallyNormedField R K reals ->
  K ->
  K ->
  K
subtractK scalars x y =
  addK scalars x (negateK scalars y)

distanceK :
  {a : Level} ->
  {R K : Set a} ->
  {reals : RealLine R} ->
  NontriviallyNormedField R K reals ->
  K ->
  K ->
  R
distanceK scalars x y =
  normK scalars (subtractK scalars x y)

subtractE :
  {a : Level} ->
  {R K E : Set a} ->
  {reals : RealLine R} ->
  {scalars : NontriviallyNormedField R K reals} ->
  SeminormedSpace R K E reals scalars ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

distanceE :
  {a : Level} ->
  {R K E : Set a} ->
  {reals : RealLine R} ->
  {scalars : NontriviallyNormedField R K reals} ->
  SeminormedSpace R K E reals scalars ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (subtractE space x y)

NormOpenK :
  {a : Level} ->
  {R K : Set a} ->
  {reals : RealLine R} ->
  (scalars : NontriviallyNormedField R K reals) ->
  Subset K ->
  Set a
NormOpenK {R = R} {K = K} {reals = reals} scalars U =
  (center : K) ->
  U center ->
  Exists R
    (\ radius ->
      Positive reals radius
      ×
      ((point : K) ->
        StrictLess reals (distanceK scalars point center) radius ->
        U point))

ClosedBallK :
  {a : Level} ->
  {R K : Set a} ->
  {reals : RealLine R} ->
  (scalars : NontriviallyNormedField R K reals) ->
  K ->
  R ->
  Subset K
ClosedBallK {reals = reals} scalars center radius point =
  lessOrEqualR reals (distanceK scalars point center) radius

ProperNormedField :
  {a : Level} ->
  {R K : Set a} ->
  {reals : RealLine R} ->
  NontriviallyNormedField R K reals ->
  Set (lsuc a)
ProperNormedField {K = K} scalars =
  (center : K) ->
  (radius : _) ->
  CompactFor (NormOpenK scalars) (ClosedBallK scalars center radius)

NeighborhoodOfZero :
  {a : Level} ->
  {R K E : Set a} ->
  {reals : RealLine R} ->
  {scalars : NontriviallyNormedField R K reals} ->
  (space : SeminormedSpace R K E reals scalars) ->
  Subset E ->
  Set a
NeighborhoodOfZero {R = R} {E = E} {reals = reals} space s =
  Exists R
    (\ radius ->
      Positive reals radius
      ×
      ((x : E) ->
        StrictLess reals (normE space x) radius ->
        s x))

record ContinuousLinearFunctional
  {a : Level}
  {R K E : Set a}
  {reals : RealLine R}
  {scalars : NontriviallyNormedField R K reals}
  (space : SeminormedSpace R K E reals scalars) :
  Set a where

  field
    apply :
      E ->
      K

    map-add :
      (x y : E) ->
      apply (addE space x y) ≡
      addK scalars (apply x) (apply y)

    map-scale :
      (a : K) ->
      (x : E) ->
      apply (scaleE space a x) ≡
      multiplyK scalars a (apply x)

    continuous-at-zero :
      (epsilon : R) ->
      Positive reals epsilon ->
      Exists R
        (\ delta ->
          Positive reals delta
          ×
          ((x : E) ->
            StrictLess reals (normE space x) delta ->
            StrictLess reals (normK scalars (apply x)) epsilon))

open ContinuousLinearFunctional

record EvaluationConstraint
  {a : Level}
  {R E : Set a}
  (reals : RealLine R) :
  Set a where

  field
    point :
      E

    radius :
      R

    radius-positive :
      Positive reals radius

open EvaluationConstraint

SatisfiesEvaluationConstraint :
  {a : Level} ->
  {R K E : Set a} ->
  {reals : RealLine R} ->
  {scalars : NontriviallyNormedField R K reals} ->
  {space : SeminormedSpace R K E reals scalars} ->
  EvaluationConstraint {E = E} reals ->
  ContinuousLinearFunctional space ->
  ContinuousLinearFunctional space ->
  Set a
SatisfiesEvaluationConstraint
  {reals = reals}
  {scalars = scalars}
  constraint
  center
  candidate =
  StrictLess reals
    (distanceK scalars
      (apply candidate (point constraint))
      (apply center (point constraint)))
    (radius constraint)

BasicWeakStarNeighborhood :
  {a : Level} ->
  {R K E : Set a} ->
  {reals : RealLine R} ->
  {scalars : NontriviallyNormedField R K reals} ->
  {space : SeminormedSpace R K E reals scalars} ->
  List (EvaluationConstraint {E = E} reals) ->
  ContinuousLinearFunctional space ->
  Subset (ContinuousLinearFunctional space)
BasicWeakStarNeighborhood constraints center candidate =
  All
    (\ constraint ->
      SatisfiesEvaluationConstraint constraint center candidate)
    constraints

WeakStarOpen :
  {a : Level} ->
  {R K E : Set a} ->
  {reals : RealLine R} ->
  {scalars : NontriviallyNormedField R K reals} ->
  (space : SeminormedSpace R K E reals scalars) ->
  Subset (ContinuousLinearFunctional space) ->
  Set a
WeakStarOpen {R = R} {E = E} {reals = reals} space U =
  (center : ContinuousLinearFunctional space) ->
  U center ->
  Exists (List (EvaluationConstraint {E = E} reals))
    (\ constraints ->
      SubsetOf
        (BasicWeakStarNeighborhood constraints center)
        U)

Polar :
  {a : Level} ->
  {R K E : Set a} ->
  {reals : RealLine R} ->
  {scalars : NontriviallyNormedField R K reals} ->
  (space : SeminormedSpace R K E reals scalars) ->
  Subset E ->
  Subset (ContinuousLinearFunctional space)
Polar {E = E} {reals = reals} {scalars = scalars} space s functional =
  (x : E) ->
  s x ->
  lessOrEqualR reals
    (normK scalars (apply functional x))
    (oneR reals)

banach-alaoglu-theorem :
  {a : Level} ->
  Set (lsuc a)
banach-alaoglu-theorem {a} =
  (R K E : Set a) ->
  (reals : RealLine R) ->
  (scalars : NontriviallyNormedField R K reals) ->
  ProperNormedField scalars ->
  (space : SeminormedSpace R K E reals scalars) ->
  (s : Subset E) ->
  NeighborhoodOfZero space s ->
  CompactFor
    (WeakStarOpen space)
    (Polar space s)
