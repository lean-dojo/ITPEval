-- Statement-only formalization of Thousand Theorems corpus artifact Q476776,
-- "Solutions of a general quartic equation": Ferrari's four-root characterization
-- over an arbitrary field in which two is invertible. This file contains no proof.

{-# OPTIONS --safe #-}

module Q476776_solutions_of_a_general_quartic_equation where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _iff_
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

scaleF :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  Nat ->
  K ->
  K
scaleF fieldStructure n x =
  multiplyF fieldStructure (fromNatF fieldStructure n) x

product3F :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K
product3F fieldStructure x y z =
  multiplyF fieldStructure (multiplyF fieldStructure x y) z

twoN : Nat
twoN =
  suc (suc zero)

threeN : Nat
threeN =
  suc twoN

fourN : Nat
fourN =
  twoN * twoN

eightN : Nat
eightN =
  twoN * fourN

sixteenN : Nat
sixteenN =
  fourN * fourN

sixtyFourN : Nat
sixtyFourN =
  fourN * sixteenN

twoHundredFiftySixN : Nat
twoHundredFiftySixN =
  sixteenN * sixteenN

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

quarticPolynomial :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K ->
  K ->
  K
quarticPolynomial fieldStructure a b c d e x =
  addF fieldStructure
    (addF fieldStructure
      (addF fieldStructure
        (addF fieldStructure
          (multiplyF fieldStructure a (powerF fieldStructure x fourN))
          (multiplyF fieldStructure b (powerF fieldStructure x threeN)))
        (multiplyF fieldStructure c (powerF fieldStructure x twoN)))
      (multiplyF fieldStructure d x))
    e

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
      (scaleF fieldStructure eightN (multiplyF fieldStructure a c))
      (scaleF fieldStructure threeN (powerF fieldStructure b twoN)))
    (scaleF fieldStructure eightN (powerF fieldStructure a twoN))

qNumerator :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K
qNumerator fieldStructure a b c d =
  addF fieldStructure
    (subtractF fieldStructure
      (powerF fieldStructure b threeN)
      (scaleF fieldStructure fourN (product3F fieldStructure a b c)))
    (scaleF fieldStructure eightN
      (multiplyF fieldStructure (powerF fieldStructure a twoN) d))

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
    (qNumerator fieldStructure a b c d)
    (scaleF fieldStructure eightN (powerF fieldStructure a threeN))

rValue :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K ->
  K
rValue fieldStructure a b c d e =
  divideF fieldStructure
    (subtractF fieldStructure
      (subtractF fieldStructure
        (addF fieldStructure
          (scaleF fieldStructure sixteenN
            (product3F fieldStructure a (powerF fieldStructure b twoN) c))
          (scaleF fieldStructure twoHundredFiftySixN
            (multiplyF fieldStructure (powerF fieldStructure a threeN) e)))
        (scaleF fieldStructure threeN (powerF fieldStructure b fourN)))
      (scaleF fieldStructure sixtyFourN
        (product3F fieldStructure
          (powerF fieldStructure a twoN) b d)))
    (scaleF fieldStructure twoHundredFiftySixN
      (powerF fieldStructure a fourN))

resolventValue :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K
resolventValue fieldStructure p q r u =
  subtractF fieldStructure
    (addF fieldStructure
      (subtractF fieldStructure
        (subtractF fieldStructure
          (powerF fieldStructure u threeN)
          (multiplyF fieldStructure p (powerF fieldStructure u twoN)))
        (scaleF fieldStructure fourN (multiplyF fieldStructure r u)))
      (scaleF fieldStructure fourN (multiplyF fieldStructure p r)))
    (powerF fieldStructure q twoN)

quarticOffset :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K
quarticOffset fieldStructure a b =
  divideF fieldStructure b (scaleF fieldStructure fourN a)

rootOne :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K
rootOne fieldStructure a b s v =
  subtractF fieldStructure
    (divideF fieldStructure
      (subtractF fieldStructure
        (negateF fieldStructure (scaleF fieldStructure twoN s))
        v)
      (fromNatF fieldStructure fourN))
    (quarticOffset fieldStructure a b)

rootTwo :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K
rootTwo fieldStructure a b s v =
  subtractF fieldStructure
    (divideF fieldStructure
      (addF fieldStructure
        (negateF fieldStructure (scaleF fieldStructure twoN s))
        v)
      (fromNatF fieldStructure fourN))
    (quarticOffset fieldStructure a b)

rootThree :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K
rootThree fieldStructure a b s w =
  subtractF fieldStructure
    (divideF fieldStructure
      (subtractF fieldStructure (scaleF fieldStructure twoN s) w)
      (fromNatF fieldStructure fourN))
    (quarticOffset fieldStructure a b)

rootFour :
  {a : Level} ->
  {K : Set a} ->
  Field K ->
  K ->
  K ->
  K ->
  K ->
  K
rootFour fieldStructure a b s w =
  subtractF fieldStructure
    (divideF fieldStructure
      (addF fieldStructure (scaleF fieldStructure twoN s) w)
      (fromNatF fieldStructure fourN))
    (quarticOffset fieldStructure a b)

solutions-of-a-general-quartic-equation :
  (a : Level) ->
  Set (lsuc a)
solutions-of-a-general-quartic-equation a =
  (K : Set a) ->
  (fieldStructure : Field K) ->
  (two-invertible :
    Invertible fieldStructure (fromNatF fieldStructure twoN)) ->
  (a b c d e p q r u s v w x : K) ->
  a != zeroF fieldStructure ->
  p == pValue fieldStructure a b c ->
  q == qValue fieldStructure a b c d ->
  q != zeroF fieldStructure ->
  r == rValue fieldStructure a b c d e ->
  resolventValue fieldStructure p q r u == zeroF fieldStructure ->
  powerF fieldStructure s twoN ==
    subtractF fieldStructure u p ->
  powerF fieldStructure v twoN ==
    subtractF fieldStructure
      (scaleF fieldStructure fourN (powerF fieldStructure s twoN))
      (scaleF fieldStructure eightN
        (subtractF fieldStructure u (divideF fieldStructure q s))) ->
  powerF fieldStructure w twoN ==
    subtractF fieldStructure
      (scaleF fieldStructure fourN (powerF fieldStructure s twoN))
      (scaleF fieldStructure eightN
        (addF fieldStructure u (divideF fieldStructure q s))) ->
  (quarticPolynomial fieldStructure a b c d e x == zeroF fieldStructure)
  iff
  ((x == rootOne fieldStructure a b s v)
    or
    (x == rootTwo fieldStructure a b s v)
    or
    (x == rootThree fieldStructure a b s w)
    or
    (x == rootFour fieldStructure a b s w))
