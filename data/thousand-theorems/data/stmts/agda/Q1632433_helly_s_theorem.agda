-- Statement-only formalization of thousand-theorems corpus artifact Q1632433,
-- "Helly's theorem": a sufficiently large finite family of convex sets in a
-- finite-dimensional vector space has nonempty total intersection when every
-- subfamily of dimension plus one has nonempty intersection. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Q1632433_helly_s_theorem where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record LinearOrderedField
  {k : Level}
  (K : Set k) :
  Set (lsuc k) where

  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK inverseK : K -> K
    lessOrEqualK : K -> K -> Set k

    one-not-zero :
      oneK != zeroK

    add-commutative :
      (x y : K) ->
      addK x y == addK y x
    add-associative :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-zero :
      (x : K) ->
      addK x zeroK == x
    add-inverse :
      (x : K) ->
      addK x (negateK x) == zeroK

    multiply-commutative :
      (x y : K) ->
      multiplyK x y == multiplyK y x
    multiply-associative :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ==
      multiplyK x (multiplyK y z)
    multiply-one :
      (x : K) ->
      multiplyK x oneK == x
    multiply-zero :
      (x : K) ->
      multiplyK x zeroK == zeroK
    distribute :
      (x y z : K) ->
      multiplyK x (addK y z) ==
      addK (multiplyK x y) (multiplyK x z)
    inverse-zero :
      inverseK zeroK == zeroK
    multiply-inverse :
      (x : K) ->
      x != zeroK ->
      multiplyK x (inverseK x) == oneK

    order-reflexive :
      (x : K) ->
      lessOrEqualK x x
    order-transitive :
      (x y z : K) ->
      lessOrEqualK x y ->
      lessOrEqualK y z ->
      lessOrEqualK x z
    order-antisymmetric :
      (x y : K) ->
      lessOrEqualK x y ->
      lessOrEqualK y x ->
      x == y
    order-total :
      (x y : K) ->
      lessOrEqualK x y or lessOrEqualK y x
    add-order :
      (x y z : K) ->
      lessOrEqualK x y ->
      lessOrEqualK (addK z x) (addK z y)
    multiply-nonnegative :
      (x y : K) ->
      lessOrEqualK zeroK x ->
      lessOrEqualK zeroK y ->
      lessOrEqualK zeroK (multiplyK x y)
    zero-less-than-one :
      lessOrEqualK zeroK oneK and zeroK != oneK

open LinearOrderedField

record VectorSpace
  {k e : Level}
  {K : Set k}
  (orderedField : LinearOrderedField K)
  (E : Set e) :
  Set (lsuc (k ⊔ e)) where

  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : K -> E -> E

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
      scaleE (oneK orderedField) x == x
    scale-associative :
      (a b : K) ->
      (x : E) ->
      scaleE (multiplyK orderedField a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectors :
      (a : K) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalars :
      (a b : K) ->
      (x : E) ->
      scaleE (addK orderedField a b) x ==
      addE (scaleE a x) (scaleE b x)
    scale-zero-vector :
      (a : K) ->
      scaleE a zeroE == zeroE
    scale-zero-scalar :
      (x : E) ->
      scaleE (zeroK orderedField) x == zeroE

open VectorSpace

sumScaled :
  {k e : Level}
  {K : Set k}
  {E : Set e}
  {orderedField : LinearOrderedField K} ->
  VectorSpace orderedField E ->
  {n : Nat} ->
  (Fin n -> K) ->
  (Fin n -> E) ->
  E
sumScaled space {zero} coefficients vectors =
  zeroE space
sumScaled space {suc n} coefficients vectors =
  addE space
    (scaleE space (coefficients fzero) (vectors fzero))
    (sumScaled space
      (\ j -> coefficients (fsuc j))
      (\ j -> vectors (fsuc j)))

record FiniteDimensional
  {k e : Level}
  {K : Set k}
  {E : Set e}
  (orderedField : LinearOrderedField K)
  (space : VectorSpace orderedField E) :
  Set (lsuc (k ⊔ e)) where

  field
    dimension : Nat
    basis : Fin dimension -> E
    basis-independent :
      (coefficients : Fin dimension -> K) ->
      sumScaled space coefficients basis == zeroE space ->
      (j : Fin dimension) ->
      coefficients j == zeroK orderedField
    basis-spans :
      (x : E) ->
      Exists (Fin dimension -> K)
        (\ coefficients ->
          sumScaled space coefficients basis == x)

open FiniteDimensional

record FiniteSubset
  {i : Level}
  (I : Set i) :
  Set (lsuc i) where

  field
    size : Nat
    member : I -> Set i
    enumerate : Fin size -> I
    enumerate-member :
      (j : Fin size) ->
      member (enumerate j)
    no-duplicates :
      (j l : Fin size) ->
      enumerate j == enumerate l ->
      j == l
    exhaustive :
      (x : I) ->
      member x ->
      Exists (Fin size)
        (\ j -> enumerate j == x)

open FiniteSubset

SubsetOf :
  {i : Level}
  {I : Set i} ->
  FiniteSubset I ->
  FiniteSubset I ->
  Set i
SubsetOf {I = I} child parent =
  (x : I) ->
  member child x ->
  member parent x

Convex :
  {k e : Level}
  {K : Set k}
  {E : Set e} ->
  (orderedField : LinearOrderedField K) ->
  VectorSpace orderedField E ->
  (E -> Set e) ->
  Set (k ⊔ e)
Convex {K = K} {E = E} orderedField space subset =
  (a b : K) ->
  lessOrEqualK orderedField (zeroK orderedField) a ->
  lessOrEqualK orderedField (zeroK orderedField) b ->
  addK orderedField a b == oneK orderedField ->
  (x y : E) ->
  subset x ->
  subset y ->
  subset
    (addE space
      (scaleE space a x)
      (scaleE space b y))

IntersectionNonempty :
  {i e : Level}
  {I : Set i}
  {E : Set e} ->
  (I -> E -> Set e) ->
  FiniteSubset I ->
  Set (i ⊔ e)
IntersectionNonempty {I = I} {E = E} family subfamily =
  Exists E
    (\ point ->
      (index : I) ->
      member subfamily index ->
      family index point)

helly-s-theorem : Setω
helly-s-theorem =
  {i k e : Level} ->
  (I : Set i) ->
  (K : Set k) ->
  (orderedField : LinearOrderedField K) ->
  (E : Set e) ->
  (space : VectorSpace orderedField E) ->
  (finiteDimension : FiniteDimensional orderedField space) ->
  (family : I -> E -> Set e) ->
  (s : FiniteSubset I) ->
  suc (dimension finiteDimension) <=N size s ->
  ((index : I) ->
    member s index ->
    Convex orderedField space (family index)) ->
  ((subfamily : FiniteSubset I) ->
    SubsetOf subfamily s ->
    size subfamily == suc (dimension finiteDimension) ->
    IntersectionNonempty family subfamily) ->
  IntersectionNonempty family s
