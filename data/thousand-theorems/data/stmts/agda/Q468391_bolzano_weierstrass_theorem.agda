-- Statement-only formalization of thousand-theorems corpus artifact Q468391,
-- "Bolzano–Weierstrass theorem": in a proper pseudometric space, a sequence
-- that is frequently contained in a bounded set, and hence any sequence
-- contained in that set, has a convergent strictly monotone subsequence whose
-- limit lies in the set's closure. This file contains no proof.

{-# OPTIONS --safe #-}

module Q468391_bolzano_weierstrass_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

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

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

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

data _<=N_ : Nat -> Nat -> Set where

  zero<= :
    {n : Nat} ->
    zero <=N n

  suc<=suc :
    {m n : Nat} ->
    m <=N n ->
    suc m <=N suc n

data _<N_ : Nat -> Nat -> Set where

  zero<suc :
    {n : Nat} ->
    zero <N suc n

  suc<suc :
    {m n : Nat} ->
    m <N n ->
    suc m <N suc n

-- A complete Archimedean ordered field is a presentation of the real line.
record RealLine
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

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
      Set r

    fromNatR :
      Nat ->
      R

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

    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)

    multiply-one :
      (x : R) ->
      multiplyR x oneR == x

    multiply-zero :
      (x : R) ->
      multiplyR x zeroR == zeroR

    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) == addR (multiplyR x y) (multiplyR x z)

    multiply-reciprocal :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexive :
      (x : R) ->
      lessOrEqualR x x

    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z

    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y

    order-total :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)

    add-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)

    multiply-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)

    zero-less-than-one :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNatR zero == zeroR

    fromNat-successor :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR

    fromNat-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Σ Nat (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : R -> Set r) ->
      Σ R P ->
      Σ R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Σ R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open RealLine

StrictLess :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  R ->
  R ->
  Set r
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

record PseudoMetricSpace
  {r a : Level}
  {R : Set r}
  (reals : RealLine R)
  (X : Set a) :
  Set (r ⊔ a) where

  field
    distance :
      X ->
      X ->
      R

    distance-nonnegative :
      (x y : X) ->
      lessOrEqualR reals (zeroR reals) (distance x y)

    distance-self :
      (x : X) ->
      distance x x == zeroR reals

    distance-symmetric :
      (x y : X) ->
      distance x y == distance y x

    distance-triangle :
      (x y z : X) ->
      lessOrEqualR reals
        (distance x z)
        (addR reals (distance x y) (distance y z))

open PseudoMetricSpace

Subset :
  {a p : Level} ->
  Set a ->
  Set (a ⊔ lsuc p)
Subset {p = p} X =
  X -> Set p

Family :
  {a p : Level} ->
  Set a ->
  Set (a ⊔ lsuc p)
Family {p = p} X =
  Subset {p = p} X -> Set p

Complement :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Subset {p = p} X
Complement U x =
  Not (U x)

MetricOpen :
  {r a : Level} ->
  {R : Set r} ->
  {X : Set a} ->
  {reals : RealLine R} ->
  PseudoMetricSpace reals X ->
  Subset {p = r} X ->
  Set (r ⊔ a)
MetricOpen {R = R} {X = X} {reals = reals} metric U =
  (center : X) ->
  U center ->
  Σ R
    (\ radius ->
      StrictLess reals (zeroR reals) radius
      and
      ((point : X) ->
        StrictLess reals (distance metric center point) radius ->
        U point))

Covers :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Family {p = p} X ->
  Set (a ⊔ lsuc p)
Covers {p = p} {X = X} U cover =
  (x : X) ->
  U x ->
  Σ (Subset {p = p} X)
    (\ V ->
      cover V and V x)

FiniteSubcover :
  {a p : Level} ->
  {X : Set a} ->
  Subset {p = p} X ->
  Family {p = p} X ->
  Set (a ⊔ lsuc p)
FiniteSubcover {p = p} {X = X} U cover =
  Σ (List (Subset {p = p} X))
    (\ selected ->
      ((V : Subset {p = p} X) ->
        Member V selected ->
        cover V)
      and
      ((x : X) ->
        U x ->
        Σ (Subset {p = p} X)
          (\ V ->
            Member V selected and V x)))

Compact :
  {r a : Level} ->
  {R : Set r} ->
  {X : Set a} ->
  {reals : RealLine R} ->
  PseudoMetricSpace reals X ->
  Subset {p = r} X ->
  Set (a ⊔ lsuc r)
Compact {r = r} {X = X} metric U =
  (cover : Family {p = r} X) ->
  ((V : Subset {p = r} X) ->
    cover V ->
    MetricOpen metric V) ->
  Covers U cover ->
  FiniteSubcover U cover

ClosedBall :
  {r a : Level} ->
  {R : Set r} ->
  {X : Set a} ->
  {reals : RealLine R} ->
  PseudoMetricSpace reals X ->
  X ->
  R ->
  Subset {p = r} X
ClosedBall {reals = reals} metric center radius point =
  lessOrEqualR reals (distance metric center point) radius

Proper :
  {r a : Level} ->
  {R : Set r} ->
  {X : Set a} ->
  {reals : RealLine R} ->
  PseudoMetricSpace reals X ->
  Set (a ⊔ lsuc r)
Proper {R = R} {X = X} metric =
  (center : X) ->
  (radius : R) ->
  Compact metric (ClosedBall metric center radius)

IsBounded :
  {r a : Level} ->
  {R : Set r} ->
  {X : Set a} ->
  {reals : RealLine R} ->
  PseudoMetricSpace reals X ->
  Subset {p = r} X ->
  Set (r ⊔ a)
IsBounded {R = R} {X = X} {reals = reals} metric U =
  Σ R
    (\ bound ->
      (x y : X) ->
      U x ->
      U y ->
      lessOrEqualR reals (distance metric x y) bound)

Closure :
  {r a : Level} ->
  {R : Set r} ->
  {X : Set a} ->
  {reals : RealLine R} ->
  PseudoMetricSpace reals X ->
  Subset {p = r} X ->
  Subset {p = r ⊔ a} X
Closure {R = R} {X = X} {reals = reals} metric U limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Σ X
    (\ point ->
      U point
      and
      StrictLess reals (distance metric limit point) epsilon)

FrequentlyAtTop :
  {a p : Level} ->
  {X : Set a} ->
  (Nat -> X) ->
  Subset {p = p} X ->
  Set p
FrequentlyAtTop sequence U =
  (cutoff : Nat) ->
  Σ Nat
    (\ n ->
      cutoff <=N n
      and
      U (sequence n))

StrictMono :
  (Nat -> Nat) ->
  Set
StrictMono subsequence =
  (m n : Nat) ->
  m <N n ->
  subsequence m <N subsequence n

ConvergesTo :
  {r a : Level} ->
  {R : Set r} ->
  {X : Set a} ->
  {reals : RealLine R} ->
  PseudoMetricSpace reals X ->
  (Nat -> X) ->
  X ->
  Set r
ConvergesTo {R = R} {reals = reals} metric sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Σ Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (distance metric (sequence n) limit) epsilon)

HasConvergentSubsequenceInClosure :
  {r a : Level} ->
  {R : Set r} ->
  {X : Set a} ->
  {reals : RealLine R} ->
  (metric : PseudoMetricSpace reals X) ->
  Subset {p = r} X ->
  (Nat -> X) ->
  Set (r ⊔ a)
HasConvergentSubsequenceInClosure {X = X} metric U sequence =
  Σ X
    (\ limit ->
      Closure metric U limit
      and
      Σ (Nat -> Nat)
        (\ subsequence ->
          StrictMono subsequence
          and
          ConvergesTo metric
            (\ n -> sequence (subsequence n))
            limit))

tendsto-subseq-of-frequently-bounded :
  {r a : Level} ->
  Set (lsuc (r ⊔ a))
tendsto-subseq-of-frequently-bounded {r} {a} =
  (R : Set r) ->
  (reals : RealLine R) ->
  (X : Set a) ->
  (metric : PseudoMetricSpace reals X) ->
  Proper metric ->
  (U : Subset {p = r} X) ->
  IsBounded metric U ->
  (sequence : Nat -> X) ->
  FrequentlyAtTop sequence U ->
  HasConvergentSubsequenceInClosure metric U sequence

tendsto-subseq-of-bounded :
  {r a : Level} ->
  Set (lsuc (r ⊔ a))
tendsto-subseq-of-bounded {r} {a} =
  (R : Set r) ->
  (reals : RealLine R) ->
  (X : Set a) ->
  (metric : PseudoMetricSpace reals X) ->
  Proper metric ->
  (U : Subset {p = r} X) ->
  IsBounded metric U ->
  (sequence : Nat -> X) ->
  ((n : Nat) -> U (sequence n)) ->
  HasConvergentSubsequenceInClosure metric U sequence
