-- Statement-only formalization of thousand-theorems corpus artifact Q1097021,
-- "Minkowski's theorem": a convex origin-symmetric set in a finite-dimensional
-- real normed space whose Haar measure exceeds 2^dimension times a lattice
-- fundamental-domain measure contains a nonzero lattice point.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1097021_minkowski_s_theorem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR absoluteR : R -> R
    lessThanR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) ->
      addR x y == addR y x
    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zero :
      (x : R) ->
      addR x zeroR == x
    add-inverse :
      (x : R) ->
      addR x (negateR x) == zeroR
    negate-involutive :
      (x : R) ->
      negateR (negateR x) == x

    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zero :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zero :
      inverseR zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-irreflexive :
      (x : R) ->
      lessThanR x x ->
      Bottom
    order-transitive :
      (x y z : R) ->
      lessThanR x y ->
      lessThanR y z ->
      lessThanR x z
    order-trichotomy :
      (x y : R) ->
      lessThanR x y or
      (x == y or lessThanR y x)
    add-order :
      (x y z : R) ->
      lessThanR x y ->
      lessThanR (addR z x) (addR z y)
    multiply-positive :
      (x y : R) ->
      lessThanR zeroR x ->
      lessThanR zeroR y ->
      lessThanR zeroR (multiplyR x y)
    zero-less-than-one :
      lessThanR zeroR oneR

    absolute-nonnegative :
      (x : R) ->
      lessThanR zeroR (absoluteR x) or absoluteR x == zeroR
    absolute-of-nonnegative :
      (x : R) ->
      (lessThanR zeroR x or zeroR == x) ->
      absoluteR x == x
    absolute-of-nonpositive :
      (x : R) ->
      (lessThanR x zeroR or x == zeroR) ->
      absoluteR x == negateR x
    absolute-zero-only :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR
    absolute-negate :
      (x : R) ->
      absoluteR (negateR x) == absoluteR x
    absolute-multiply :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)
    absolute-triangle :
      (x y : R) ->
      lessThanR (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y)) or
      absoluteR (addR x y) ==
        addR (absoluteR x) (absoluteR y)

    fromNat-zero :
      fromNatR zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNatR (m + n) ==
      addR (fromNatR m) (fromNatR n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) ==
      multiplyR (fromNatR m) (fromNatR n)
    fromNat-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessThanR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessThanR x upper or x == upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessThanR x supremum or x == supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessThanR x upper or x == upper) ->
            lessThanR supremum upper or supremum == upper))

open CompleteOrderedField

LessOrEqual :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
LessOrEqual reals x y =
  lessThanR reals x y or x == y

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

powerR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  oneR reals
powerR reals x (suc n) =
  multiplyR reals x (powerR reals x n)

twoPowerR :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
twoPowerR reals n =
  powerR reals
    (addR reals (oneR reals) (oneR reals))
    n

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) :
  Set1 where

  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) ->
      forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) ->
      backwardR (forwardR x) == x
    forward-zeroR :
      forwardR (zeroR source) == zeroR target
    forward-oneR :
      forwardR (oneR source) == oneR target
    forward-addR :
      (x y : R) ->
      forwardR (addR source x y) ==
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) ->
      forwardR (multiplyR source x y) ==
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) ->
      forwardR (negateR source x) ==
      negateR target (forwardR x)
    forward-inverseR :
      (x : R) ->
      forwardR (inverseR source x) ==
      inverseR target (forwardR x)
    forward-absoluteR :
      (x : R) ->
      forwardR (absoluteR source x) ==
      absoluteR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) ==
      fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessThanR source x y)
        (lessThanR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set2 where

  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

record NormedRealVectorSpace
  (R E : Set)
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : R -> E -> E
    normE : E -> R

    add-commutativeE :
      (x y : E) ->
      addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) ->
      addE x zeroE == x
    add-inverseE :
      (x : E) ->
      addE x (negateE x) == zeroE

    scale-one :
      (x : E) ->
      scaleE (oneR reals) x == x
    scale-associative :
      (a b : R) ->
      (x : E) ->
      scaleE (multiplyR reals a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectors :
      (a : R) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalars :
      (a b : R) ->
      (x : E) ->
      scaleE (addR reals a b) x ==
      addE (scaleE a x) (scaleE b x)

    norm-nonnegative :
      (x : E) ->
      LessOrEqual reals (zeroR reals) (normE x)
    norm-zero :
      normE zeroE == zeroR reals
    norm-zero-only :
      (x : E) ->
      normE x == zeroR reals ->
      x == zeroE
    norm-negate :
      (x : E) ->
      normE (negateE x) == normE x
    norm-triangle :
      (x y : E) ->
      LessOrEqual reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))
    norm-scale :
      (a : R) ->
      (x : E) ->
      normE (scaleE a x) ==
      multiplyR reals (absoluteR reals a) (normE x)

open NormedRealVectorSpace

subtractE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealVectorSpace R E reals ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

record FiniteDimensional
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedRealVectorSpace R E reals) :
  Set1 where

  field
    dimension : Nat
    coordinates : E -> Fin dimension -> R
    rebuild : (Fin dimension -> R) -> E

    rebuild-coordinates :
      (x : E) ->
      rebuild (coordinates x) == x
    coordinates-rebuild :
      (values : Fin dimension -> R) ->
      (i : Fin dimension) ->
      coordinates (rebuild values) i == values i
    coordinates-add :
      (x y : E) ->
      (i : Fin dimension) ->
      coordinates (addE space x y) i ==
      addR reals (coordinates x i) (coordinates y i)
    coordinates-scale :
      (a : R) ->
      (x : E) ->
      (i : Fin dimension) ->
      coordinates (scaleE space a x) i ==
      multiplyR reals a (coordinates x i)

open FiniteDimensional

Region : Set -> Set1
Region E =
  E -> Set

Empty :
  {E : Set} ->
  Region E
Empty _ =
  Bottom

Whole :
  {E : Set} ->
  Region E
Whole _ =
  Bottom -> Bottom

Complement :
  {E : Set} ->
  Region E ->
  Region E
Complement S x =
  Not (S x)

Intersection :
  {E : Set} ->
  Region E ->
  Region E ->
  Region E
Intersection S T x =
  S x and T x

Union :
  {E : Set} ->
  Region E ->
  Region E ->
  Region E
Union S T x =
  S x or T x

UnionAll :
  {E : Set} ->
  (Nat -> Region E) ->
  Region E
UnionAll sets x =
  Exists Nat (\ n -> sets n x)

Subset :
  {E : Set} ->
  Region E ->
  Region E ->
  Set
Subset {E = E} S T =
  (x : E) ->
  S x ->
  T x

Disjoint :
  {E : Set} ->
  Region E ->
  Region E ->
  Set
Disjoint {E = E} S T =
  (x : E) ->
  S x ->
  T x ->
  Bottom

PairwiseDisjoint :
  {E : Set} ->
  (Nat -> Region E) ->
  Set
PairwiseDisjoint sets =
  (m n : Nat) ->
  m != n ->
  Disjoint (sets m) (sets n)

translateRegion :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealVectorSpace R E reals ->
  E ->
  Region E ->
  Region E
translateRegion {E = E} space offset S x =
  Exists E
    (\ y ->
      S y and
      x == addE space offset y)

Open :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealVectorSpace R E reals ->
  Region E ->
  Set
Open {R = R} {E = E} {reals = reals} space U =
  (x : E) ->
  U x ->
  Exists R
    (\ epsilon ->
      lessThanR reals (zeroR reals) epsilon and
      ((y : E) ->
        lessThanR reals
          (normE space (subtractE space y x))
          epsilon ->
        U y))

ConvergesTo :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealVectorSpace R E reals ->
  (Nat -> E) ->
  E ->
  Set
ConvergesTo {R = R} {reals = reals} space sequence limit =
  (epsilon : R) ->
  lessThanR reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      lessThanR reals
        (normE space (subtractE space (sequence n) limit))
        epsilon)

StrictlyIncreasing :
  (Nat -> Nat) ->
  Set
StrictlyIncreasing subsequence =
  (n : Nat) ->
  subsequence n <N subsequence (suc n)

Compact :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealVectorSpace R E reals ->
  Region E ->
  Set
Compact {E = E} space K =
  (sequence : Nat -> E) ->
  ((n : Nat) -> K (sequence n)) ->
  Exists (Nat -> Nat)
    (\ subsequence ->
      StrictlyIncreasing subsequence and
      Exists E
        (\ limit ->
          ConvergesTo space
            (\ n -> sequence (subsequence n))
            limit
          and
          K limit))

Convex :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealVectorSpace R E reals ->
  Region E ->
  Set
Convex {R = R} {E = E} {reals = reals} space S =
  (x y : E) ->
  S x ->
  S y ->
  (t : R) ->
  LessOrEqual reals (zeroR reals) t ->
  LessOrEqual reals t (oneR reals) ->
  S
    (addE space
      (scaleE space t x)
      (scaleE space
        (subtractR reals (oneR reals) t)
        y))

OriginSymmetric :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealVectorSpace R E reals ->
  Region E ->
  Set
OriginSymmetric {E = E} space S =
  (x : E) ->
  S x ->
  S (negateE space x)

data Borel
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedRealVectorSpace R E reals) :
  Region E ->
  Set1 where

  open-borel :
    (U : Region E) ->
    Open space U ->
    Borel space U

  complement-borel :
    {S : Region E} ->
    Borel space S ->
    Borel space (Complement S)

  union-borel :
    (sets : Nat -> Region E) ->
    ((n : Nat) -> Borel space (sets n)) ->
    Borel space (UnionAll sets)

  congruent-borel :
    {S T : Region E} ->
    ((x : E) -> Iff (S x) (T x)) ->
    Borel space S ->
    Borel space T

record NonnegativeReal
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set where

  constructor nonnegative-real
  field
    realValue :
      R
    realValue-nonnegative :
      LessOrEqual reals (zeroR reals) realValue

open NonnegativeReal

record ExtendedNonnegativeReals
  (R M : Set)
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    zeroM oneM infinityM :
      M
    addM multiplyM :
      M -> M -> M
    lessOrEqualM :
      M -> M -> Set
    finiteM :
      (x : R) ->
      LessOrEqual reals (zeroR reals) x ->
      M

    zero-leastM :
      (x : M) ->
      lessOrEqualM zeroM x
    infinity-greatestM :
      (x : M) ->
      lessOrEqualM x infinityM
    infinity-not-zeroM :
      infinityM != zeroM
    one-not-zeroM :
      oneM != zeroM
    order-reflexiveM :
      (x : M) ->
      lessOrEqualM x x
    order-transitiveM :
      (x y z : M) ->
      lessOrEqualM x y ->
      lessOrEqualM y z ->
      lessOrEqualM x z
    order-antisymmetricM :
      (x y : M) ->
      lessOrEqualM x y ->
      lessOrEqualM y x ->
      x == y
    order-totalM :
      (x y : M) ->
      lessOrEqualM x y or lessOrEqualM y x

    add-commutativeM :
      (x y : M) ->
      addM x y == addM y x
    add-associativeM :
      (x y z : M) ->
      addM (addM x y) z == addM x (addM y z)
    add-zeroM :
      (x : M) ->
      addM x zeroM == x
    add-infinityM :
      (x : M) ->
      addM x infinityM == infinityM
    add-monotoneM :
      (w x y z : M) ->
      lessOrEqualM w x ->
      lessOrEqualM y z ->
      lessOrEqualM (addM w y) (addM x z)

    multiply-commutativeM :
      (x y : M) ->
      multiplyM x y == multiplyM y x
    multiply-associativeM :
      (x y z : M) ->
      multiplyM (multiplyM x y) z ==
      multiplyM x (multiplyM y z)
    multiply-oneM :
      (x : M) ->
      multiplyM x oneM == x
    multiply-zeroM :
      (x : M) ->
      multiplyM x zeroM == zeroM
    multiply-distributesM :
      (x y z : M) ->
      multiplyM x (addM y z) ==
      addM (multiplyM x y) (multiplyM x z)
    multiply-monotoneM :
      (w x y z : M) ->
      lessOrEqualM w x ->
      lessOrEqualM y z ->
      lessOrEqualM
        (multiplyM w y)
        (multiplyM x z)
    multiply-infinity-nonzeroM :
      (x : M) ->
      x != zeroM ->
      multiplyM x infinityM == infinityM

    finite-zeroM :
      (hzero : LessOrEqual reals (zeroR reals) (zeroR reals)) ->
      finiteM (zeroR reals) hzero == zeroM
    finite-oneM :
      (hone : LessOrEqual reals (zeroR reals) (oneR reals)) ->
      finiteM (oneR reals) hone == oneM
    finite-orderM :
      (x y : R) ->
      (hx : LessOrEqual reals (zeroR reals) x) ->
      (hy : LessOrEqual reals (zeroR reals) y) ->
      Iff
        (lessOrEqualM (finiteM x hx) (finiteM y hy))
        (LessOrEqual reals x y)
    finite-addM :
      (x y : R) ->
      (hx : LessOrEqual reals (zeroR reals) x) ->
      (hy : LessOrEqual reals (zeroR reals) y) ->
      Exists
        (LessOrEqual reals
          (zeroR reals)
          (addR reals x y))
        (\ hsum ->
          addM (finiteM x hx) (finiteM y hy) ==
          finiteM (addR reals x y) hsum)
    finite-multiplyM :
      (x y : R) ->
      (hx : LessOrEqual reals (zeroR reals) x) ->
      (hy : LessOrEqual reals (zeroR reals) y) ->
      Exists
        (LessOrEqual reals
          (zeroR reals)
          (multiplyR reals x y))
        (\ hproduct ->
          multiplyM (finiteM x hx) (finiteM y hy) ==
          finiteM (multiplyR reals x y) hproduct)
    finite-or-infinityM :
      (x : M) ->
      x == infinityM or
      Exists R
        (\ value ->
          Exists
            (LessOrEqual reals (zeroR reals) value)
            (\ nonnegative ->
              x == finiteM value nonnegative))

open ExtendedNonnegativeReals

finiteNN :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  NonnegativeReal reals ->
  M
finiteNN extended x =
  finiteM extended
    (realValue x)
    (realValue-nonnegative x)

StrictLessM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  M ->
  M ->
  Set
StrictLessM extended x y =
  lessOrEqualM extended x y and x != y

powerM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  M ->
  Nat ->
  M
powerM extended x zero =
  oneM extended
powerM extended x (suc n) =
  multiplyM extended x (powerM extended x n)

sumFirstM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  Nat ->
  (Nat -> M) ->
  M
sumFirstM extended zero term =
  zeroM extended
sumFirstM extended (suc n) term =
  addM extended
    (sumFirstM extended n term)
    (term n)

CountableSum :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  (Nat -> M) ->
  M ->
  Set
CountableSum extended terms value =
  ((n : Nat) ->
    lessOrEqualM extended
      (sumFirstM extended n terms)
      value)
  and
  ((upper : _) ->
    ((n : Nat) ->
      lessOrEqualM extended
        (sumFirstM extended n terms)
        upper) ->
    lessOrEqualM extended value upper)

data CanonicalENNReal
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set where

  finite-ennreal :
    NonnegativeReal reals ->
    CanonicalENNReal reals
  infinity-ennreal :
    CanonicalENNReal reals

CanonicalENNRealLe :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  CanonicalENNReal reals ->
  CanonicalENNReal reals ->
  Set
CanonicalENNRealLe
  {reals = reals}
  (finite-ennreal x)
  (finite-ennreal y) =
  LessOrEqual reals (realValue x) (realValue y)
CanonicalENNRealLe (finite-ennreal x) infinity-ennreal =
  Top
CanonicalENNRealLe infinity-ennreal (finite-ennreal y) =
  Bottom
CanonicalENNRealLe infinity-ennreal infinity-ennreal =
  Top

record ENNRealPresentation
  {R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals) :
  Set1 where

  field
    toCanonicalENNReal :
      M ->
      CanonicalENNReal reals
    fromCanonicalENNReal :
      CanonicalENNReal reals ->
      M
    to-after-fromENNReal :
      (x : CanonicalENNReal reals) ->
      toCanonicalENNReal (fromCanonicalENNReal x) == x
    from-after-toENNReal :
      (x : M) ->
      fromCanonicalENNReal (toCanonicalENNReal x) == x
    finite-correspondenceENNReal :
      (x : NonnegativeReal reals) ->
      toCanonicalENNReal (finiteNN extended x) ==
      finite-ennreal x
    infinity-correspondenceENNReal :
      toCanonicalENNReal (infinityM extended) ==
      infinity-ennreal
    order-correspondenceENNReal :
      (x y : M) ->
      Iff
        (lessOrEqualM extended x y)
        (CanonicalENNRealLe
          (toCanonicalENNReal x)
          (toCanonicalENNReal y))

record BorelMeasure
  {R E M : Set}
  {reals : CompleteOrderedField R}
  (space : NormedRealVectorSpace R E reals)
  (extended : ExtendedNonnegativeReals R M reals) :
  Set1 where

  field
    mass :
      Region E ->
      M

    mass-congruent :
      (S T : Region E) ->
      ((x : E) -> Iff (S x) (T x)) ->
      mass S == mass T
    mass-empty :
      mass Empty == zeroM extended
    mass-nonnegative :
      (S : Region E) ->
      lessOrEqualM extended
        (zeroM extended)
        (mass S)
    mass-monotone :
      (S T : Region E) ->
      Subset S T ->
      lessOrEqualM extended (mass S) (mass T)
    mass-countable-subadditive :
      (sets : Nat -> Region E) ->
      (sumValue : M) ->
      CountableSum extended
        (\ n -> mass (sets n))
        sumValue ->
      lessOrEqualM extended
        (mass (UnionAll sets))
        sumValue
    borel-caratheodory :
      (S : Region E) ->
      Borel space S ->
      (T : Region E) ->
      mass T ==
      addM extended
        (mass (Intersection T S))
        (mass (Intersection T (Complement S)))
    mass-countable-additive :
      (sets : Nat -> Region E) ->
      ((n : Nat) -> Borel space (sets n)) ->
      PairwiseDisjoint sets ->
      CountableSum extended
        (\ n -> mass (sets n))
        (mass (UnionAll sets))

open BorelMeasure

AlmostEverywhere :
  {R E M : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : NormedRealVectorSpace R E reals} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  BorelMeasure space extended ->
  Region E ->
  Set
AlmostEverywhere {extended = extended} measure P =
  mass measure (Complement P) == zeroM extended

AEDisjoint :
  {R E M : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : NormedRealVectorSpace R E reals} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  BorelMeasure space extended ->
  Region E ->
  Region E ->
  Set
AEDisjoint {extended = extended} measure S T =
  mass measure (Intersection S T) == zeroM extended

SymmetricDifference :
  {E : Set} ->
  Region E ->
  Region E ->
  Region E
SymmetricDifference S T =
  Union
    (Intersection S (Complement T))
    (Intersection T (Complement S))

record NullMeasurable
  {R E M : Set}
  {reals : CompleteOrderedField R}
  {space : NormedRealVectorSpace R E reals}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : BorelMeasure space extended)
  (S : Region E) :
  Set1 where

  field
    measurable-representative :
      Region E
    representative-borel :
      Borel space measurable-representative
    null-envelope :
      Region E
    null-envelope-borel :
      Borel space null-envelope
    null-envelope-has-zero-mass :
      mass measure null-envelope ==
      zeroM extended
    symmetric-difference-contained-in-null-envelope :
      Subset
        (SymmetricDifference S measurable-representative)
        null-envelope

record IsAddHaarMeasure
  {R E M : Set}
  {reals : CompleteOrderedField R}
  (space : NormedRealVectorSpace R E reals)
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : BorelMeasure space extended) :
  Set1 where

  field
    left-invariant :
      (offset : E) ->
      (S : Region E) ->
      Borel space S ->
      mass measure (translateRegion space offset S) ==
      mass measure S

    finite-on-compacts :
      (K : Region E) ->
      Compact space K ->
      mass measure K != infinityM extended

    positive-on-nonempty-open :
      (U : Region E) ->
      Open space U ->
      Exists E U ->
      mass measure U != zeroM extended

record AddSubgroup
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedRealVectorSpace R E reals) :
  Set1 where

  field
    contains : E -> Set
    contains-zero :
      contains (zeroE space)
    contains-add :
      (x y : E) ->
      contains x ->
      contains y ->
      contains (addE space x y)
    contains-negate :
      (x : E) ->
      contains x ->
      contains (negateE space x)

open AddSubgroup

record CountableSubgroup
  {R E : Set}
  {reals : CompleteOrderedField R}
  {space : NormedRealVectorSpace R E reals}
  (lattice : AddSubgroup space) :
  Set1 where

  field
    enumerate :
      Nat -> E
    enumerate-in-lattice :
      (n : Nat) ->
      contains lattice (enumerate n)
    enumerate-surjective :
      (x : E) ->
      contains lattice x ->
      Exists Nat (\ n -> enumerate n == x)

record IsAddFundamentalDomain
  {R E M : Set}
  {reals : CompleteOrderedField R}
  {space : NormedRealVectorSpace R E reals}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : BorelMeasure space extended)
  (lattice : AddSubgroup space)
  (F : Region E) :
  Set1 where

  field
    null-measurable :
      NullMeasurable measure F

    ae-covers :
      AlmostEverywhere measure
        (\ x ->
          Exists E
            (\ g ->
              contains lattice g and
              F (addE space g x)))

    pairwise-ae-disjoint :
      (g h : E) ->
      contains lattice g ->
      contains lattice h ->
      g != h ->
      AEDisjoint measure
        (translateRegion space g F)
        (translateRegion space h F)

minkowski-s-theorem : Set2
minkowski-s-theorem =
  (R E M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (space : NormedRealVectorSpace R E reals) ->
  (finite-dimensional : FiniteDimensional space) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : BorelMeasure space extended) ->
  IsAddHaarMeasure space extended measure ->
  (lattice : AddSubgroup space) ->
  CountableSubgroup lattice ->
  (F s : Region E) ->
  IsAddFundamentalDomain measure lattice F ->
  OriginSymmetric space s ->
  Convex space s ->
  StrictLessM extended
    (multiplyM extended
      (mass measure F)
      (powerM extended
        (addM extended
          (oneM extended)
          (oneM extended))
        (dimension finite-dimensional)))
    (mass measure s) ->
  Exists E
    (\ x ->
      x != zeroE space and
      (contains lattice x and s x))
