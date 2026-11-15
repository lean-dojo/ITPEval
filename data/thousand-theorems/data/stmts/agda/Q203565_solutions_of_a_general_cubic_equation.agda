-- Statement-only formalization of Thousand Theorems corpus artifact Q203565,
-- "Solutions of a general cubic equation": Cardano's three-root characterization
-- over a field of characteristic neither two nor three. This file contains no proof.

{-# OPTIONS --safe #-}

module Q203565_solutions_of_a_general_cubic_equation where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _iff_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

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
  (P : Set a)
  (Q : Set b) :
  Set (a ⊔ b) where

  constructor both
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

  constructor equivalence
  field
    forward  : P -> Q
    backward : Q -> P

record Field
  {a : Level}
  (K : Set a) :
  Set a where

  field
    zeroF oneF : K
    addF multiplyF : K -> K -> K
    negateF inverseF : K -> K

    one-not-zero :
      oneF != zeroF

    add-commutative :
      (x y : K) ->
      addF x y == addF y x
    add-associative :
      (x y z : K) ->
      addF (addF x y) z == addF x (addF y z)
    add-zero :
      (x : K) ->
      addF x zeroF == x
    add-inverse :
      (x : K) ->
      addF x (negateF x) == zeroF

    multiply-commutative :
      (x y : K) ->
      multiplyF x y == multiplyF y x
    multiply-associative :
      (x y z : K) ->
      multiplyF (multiplyF x y) z ==
      multiplyF x (multiplyF y z)
    multiply-one :
      (x : K) ->
      multiplyF x oneF == x
    multiply-zero :
      (x : K) ->
      multiplyF x zeroF == zeroF
    distribute :
      (x y z : K) ->
      multiplyF x (addF y z) ==
      addF (multiplyF x y) (multiplyF x z)

    inverse-zero :
      inverseF zeroF == zeroF
    multiply-inverse :
      (x : K) ->
      x != zeroF ->
      multiplyF x (inverseF x) == oneF

open Field

subtractF :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K
subtractF fieldStructure x y =
  addF fieldStructure x (negateF fieldStructure y)

divideF :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K
divideF fieldStructure x y =
  multiplyF fieldStructure x (inverseF fieldStructure y)

fromNatF :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  Nat ->
  K
fromNatF fieldStructure zero =
  zeroF fieldStructure
fromNatF fieldStructure (suc n) =
  addF fieldStructure (fromNatF fieldStructure n) (oneF fieldStructure)

powerF :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  Nat ->
  K
powerF fieldStructure x zero =
  oneF fieldStructure
powerF fieldStructure x (suc n) =
  multiplyF fieldStructure (powerF fieldStructure x n) x

twoN : Nat
twoN =
  suc (suc zero)

threeN : Nat
threeN =
  suc twoN

nineN : Nat
nineN =
  threeN * threeN

twentySevenN : Nat
twentySevenN =
  threeN * nineN

fiftyFourN : Nat
fiftyFourN =
  twoN * twentySevenN

record Invertible
  {a : Level}
  {K : Set a}
  (fieldStructure : Field K)
  (x : K) :
  Set a where

  field
    inverse-value : K
    inverse-times-value :
      multiplyF fieldStructure inverse-value x == oneF fieldStructure

record PrimitiveCubeRoot
  {a : Level}
  {K : Set a}
  (fieldStructure : Field K)
  (omega : K) :
  Set a where

  field
    omega-cubed-is-one :
      powerF fieldStructure omega threeN == oneF fieldStructure
    omega-is-not-one :
      omega != oneF fieldStructure

cubicPolynomial :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K ->
  K
cubicPolynomial fieldStructure a b c d x =
  addF fieldStructure
    (addF fieldStructure
      (addF fieldStructure
        (multiplyF fieldStructure a (powerF fieldStructure x threeN))
        (multiplyF fieldStructure b (powerF fieldStructure x twoN)))
      (multiplyF fieldStructure c x))
    d

pValue :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K
pValue fieldStructure a b c =
  divideF fieldStructure
    (subtractF fieldStructure
      (multiplyF fieldStructure
        (multiplyF fieldStructure (fromNatF fieldStructure threeN) a)
        c)
      (powerF fieldStructure b twoN))
    (multiplyF fieldStructure
      (fromNatF fieldStructure nineN)
      (powerF fieldStructure a twoN))

qValue :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K
qValue fieldStructure a b c d =
  divideF fieldStructure
    (subtractF fieldStructure
      (subtractF fieldStructure
        (multiplyF fieldStructure
          (multiplyF fieldStructure
            (multiplyF fieldStructure (fromNatF fieldStructure nineN) a)
            b)
          c)
        (multiplyF fieldStructure
          (fromNatF fieldStructure twoN)
          (powerF fieldStructure b threeN)))
      (multiplyF fieldStructure
        (multiplyF fieldStructure
          (fromNatF fieldStructure twentySevenN)
          (powerF fieldStructure a twoN))
        d))
    (multiplyF fieldStructure
      (fromNatF fieldStructure fiftyFourN)
      (powerF fieldStructure a threeN))

rootShift :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K
rootShift fieldStructure a b =
  divideF fieldStructure b
    (multiplyF fieldStructure (fromNatF fieldStructure threeN) a)

solutions-of-a-general-cubic-equation :
  (a : Level) ->
  Set (lsuc a)
solutions-of-a-general-cubic-equation a =
  (K : Set a) ->
  (fieldStructure : Field K) ->
  (two-invertible :
    Invertible fieldStructure (fromNatF fieldStructure twoN)) ->
  (three-invertible :
    Invertible fieldStructure (fromNatF fieldStructure threeN)) ->
  (a b c d omega p q r s t x : K) ->
  a != zeroF fieldStructure ->
  PrimitiveCubeRoot fieldStructure omega ->
  p == pValue fieldStructure a b c ->
  p != zeroF fieldStructure ->
  q == qValue fieldStructure a b c d ->
  powerF fieldStructure r twoN ==
    addF fieldStructure
      (powerF fieldStructure q twoN)
      (powerF fieldStructure p threeN) ->
  powerF fieldStructure s threeN ==
    addF fieldStructure q r ->
  multiplyF fieldStructure t s == p ->
  (cubicPolynomial fieldStructure a b c d x == zeroF fieldStructure)
  iff
  ((x ==
      subtractF fieldStructure
        (subtractF fieldStructure s t)
        (rootShift fieldStructure a b))
    or
    (x ==
      subtractF fieldStructure
        (subtractF fieldStructure
          (multiplyF fieldStructure s omega)
          (multiplyF fieldStructure t (powerF fieldStructure omega twoN)))
        (rootShift fieldStructure a b))
    or
    (x ==
      subtractF fieldStructure
        (subtractF fieldStructure
          (multiplyF fieldStructure s (powerF fieldStructure omega twoN))
          (multiplyF fieldStructure t omega))
        (rootShift fieldStructure a b)))
