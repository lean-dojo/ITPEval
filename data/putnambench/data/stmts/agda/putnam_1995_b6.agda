-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_b6:
-- three Beatty sets from positive real parameters cannot be pairwise disjoint
-- while covering exactly the positive natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

oneN : Nat
oneN =
  suc zero

PositiveNat : Nat -> Set
PositiveNat n =
  oneN <=N n

intSuccessor : Int -> Int
intSuccessor (pos n) =
  pos (suc n)
intSuccessor (negsuc zero) =
  pos zero
intSuccessor (negsuc (suc n)) =
  negsuc n

embedInt :
  {R : Set} ->
  (Nat -> R) ->
  (R -> R) ->
  Int ->
  R
embedInt fromNatural negateR (pos n) =
  fromNatural n
embedInt fromNatural negateR (negsuc n) =
  negateR (fromNatural (suc n))

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R
    floor : R -> Int

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

    floor-lower :
      (x : R) ->
      lessOrEqual
        (embedInt fromNat negate (floor x))
        x
    floor-upper :
      (x : R) ->
      lessOrEqual
        x
        (embedInt fromNat negate (intSuccessor (floor x)))
      and
      x != embedInt fromNat negate (intSuccessor (floor x))

open CompleteOrderedRealField

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

NatSubset : Set1
NatSubset =
  Nat -> Set

Union :
  NatSubset ->
  NatSubset ->
  NatSubset
Union A B x =
  A x or B x

Disjoint :
  NatSubset ->
  NatSubset ->
  Set
Disjoint A B =
  (x : Nat) ->
  A x ->
  B x ->
  Bottom

SetEqual :
  NatSubset ->
  NatSubset ->
  Set
SetEqual A B =
  (x : Nat) ->
  Iff (A x) (B x)

module Putnam1995B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  BeattySet :
    R ->
    NatSubset
  BeattySet alpha x =
    Exists Nat
      (\ n ->
        PositiveNat n
        and
        pos x ==
        floor reals
          (multiply reals
            (fromNat reals n)
            alpha))

  PositiveNaturals : NatSubset
  PositiveNaturals =
    PositiveNat

  proposition : Set
  proposition =
    Not
      (Exists R
        (\ alpha ->
          Exists R
            (\ beta ->
              Exists R
                (\ gamma ->
                  StrictLess reals (zeroR reals) alpha
                  and
                  StrictLess reals (zeroR reals) beta
                  and
                  StrictLess reals (zeroR reals) gamma
                  and
                  Disjoint (BeattySet alpha) (BeattySet beta)
                  and
                  Disjoint (BeattySet beta) (BeattySet gamma)
                  and
                  Disjoint (BeattySet alpha) (BeattySet gamma)
                  and
                  SetEqual
                    PositiveNaturals
                    (Union
                      (Union
                        (BeattySet alpha)
                        (BeattySet beta))
                      (BeattySet gamma))))))

putnam-1995-b6 : Set1
putnam-1995-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1995B6Statement.proposition reals
