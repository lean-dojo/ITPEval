-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_b5
-- (putnambench__agda__putnam_1996_b5): the number of length-n X/O strings
-- whose every consecutive substring has symbol-count difference at most two.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infixr 5 _++_
infixr 4 _and_

data Symbol : Set where
  X O : Symbol

_and_ : Bool -> Bool -> Bool
true and condition = condition
false and condition = false

lessOrEqual : Nat -> Nat -> Bool
lessOrEqual zero n = true
lessOrEqual (suc m) zero = false
lessOrEqual (suc m) (suc n) = lessOrEqual m n

_++_ :
  {A : Set} ->
  List A ->
  List A ->
  List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

mapList :
  {A B : Set} ->
  (A -> B) ->
  List A ->
  List B
mapList function [] = []
mapList function (x ∷ xs) =
  function x ∷ mapList function xs

prependX : List Symbol -> List Symbol
prependX string =
  X ∷ string

prependO : List Symbol -> List Symbol
prependO string =
  O ∷ string

allStrings : Nat -> List (List Symbol)
allStrings zero =
  [] ∷ []
allStrings (suc n) =
  mapList prependX (allStrings n) ++
  mapList prependO (allStrings n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

withinTwo :
  Nat ->
  Nat ->
  Bool
withinTwo x-count o-count =
  lessOrEqual x-count (o-count + two) and
  lessOrEqual o-count (x-count + two)

allPrefixesWithinTwoFrom :
  Nat ->
  Nat ->
  List Symbol ->
  Bool
allPrefixesWithinTwoFrom x-count o-count [] =
  true
allPrefixesWithinTwoFrom x-count o-count (X ∷ string) =
  withinTwo (suc x-count) o-count and
  allPrefixesWithinTwoFrom (suc x-count) o-count string
allPrefixesWithinTwoFrom x-count o-count (O ∷ string) =
  withinTwo x-count (suc o-count) and
  allPrefixesWithinTwoFrom x-count (suc o-count) string

allPrefixesWithinTwo :
  List Symbol ->
  Bool
allPrefixesWithinTwo =
  allPrefixesWithinTwoFrom zero zero

balanced : List Symbol -> Bool
balanced [] =
  true
balanced string@(_ ∷ tail) =
  allPrefixesWithinTwo string and
  balanced tail

filterList :
  {A : Set} ->
  (A -> Bool) ->
  List A ->
  List A
filterList predicate [] =
  []
filterList predicate (x ∷ xs) with predicate x
... | true =
  x ∷ filterList predicate xs
... | false =
  filterList predicate xs

length :
  {A : Set} ->
  List A ->
  Nat
length [] =
  zero
length (_ ∷ xs) =
  suc (length xs)

numberOfBalancedStrings :
  Nat ->
  Nat
numberOfBalancedStrings n =
  length (filterList balanced (allStrings n))

naturalDiv : Nat -> Nat -> Nat
naturalDiv numerator zero =
  zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  base * power base exponent

putnam-1996-b5-solution :
  Nat ->
  Nat
putnam-1996-b5-solution n =
  power two (naturalDiv (n + two) two) +
  power two (naturalDiv (n + one) two) -
  two

putnam-1996-b5 : Set
putnam-1996-b5 =
  (n : Nat) ->
  numberOfBalancedStrings n == putnam-1996-b5-solution n
