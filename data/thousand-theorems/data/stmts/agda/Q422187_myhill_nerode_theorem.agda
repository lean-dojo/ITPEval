-- Statement-only formalization of thousand-theorems corpus artifact Q422187
-- (thousand-theorems__agda__Q422187), "Myhill–Nerode theorem": a language is
-- regular if and only if its range of left quotients is finite. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q422187_myhill_nerode_theorem where

open import Agda.Primitive using (Level; lzero; lsuc)
  renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)

infixr 5 _++_
infix 4 _iff_

record _iff_
  {a b : Level}
  (left : Set a)
  (right : Set b) :
  Set (a lmax b) where

  constructor equivalence
  field
    forward : left -> right
    backward : right -> left

record HProp (a : Level) : Set (lsuc a) where
  constructor proposition
  field
    Carrier : Set a
    carrier-is-proposition :
      (left right : Carrier) ->
      left ≡ right

open HProp using (Carrier)

_++_ :
  {a : Level} ->
  {A : Set a} ->
  List A ->
  List A ->
  List A
[] ++ ys =
  ys
(x ∷ xs) ++ ys =
  x ∷ (xs ++ ys)

Language :
  {a : Level} ->
  (p : Level) ->
  Set a ->
  Set (a lmax lsuc p)
Language p Alphabet =
  List Alphabet -> HProp p

LanguageEquivalent :
  {a p : Level} ->
  {Alphabet : Set a} ->
  Language p Alphabet ->
  Language p Alphabet ->
  Set (a lmax p)
LanguageEquivalent {Alphabet = Alphabet} left right =
  (word : List Alphabet) ->
  (Carrier (left word)) iff (Carrier (right word))

leftQuotient :
  {a p : Level} ->
  {Alphabet : Set a} ->
  Language p Alphabet ->
  List Alphabet ->
  Language p Alphabet
leftQuotient language prefix suffix =
  language (prefix ++ suffix)

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A ->
  Set a where

  here :
    {xs : List A} ->
    Member x (x ∷ xs)

  there :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    enumeration : List A
    covers :
      (x : A) ->
      Member x enumeration

record DFA
  {a s p : Level}
  (Alphabet : Set a)
  (State : Set s) :
  Set (a lmax s lmax lsuc p) where

  field
    step :
      State ->
      Alphabet ->
      State
    start :
      State
    accept :
      State ->
      HProp p

open DFA

evalFrom :
  {a s p : Level} ->
  {Alphabet : Set a} ->
  {State : Set s} ->
  DFA {p = p} Alphabet State ->
  State ->
  List Alphabet ->
  State
evalFrom automaton state [] =
  state
evalFrom automaton state (letter ∷ word) =
  evalFrom automaton (step automaton state letter) word

eval :
  {a s p : Level} ->
  {Alphabet : Set a} ->
  {State : Set s} ->
  DFA {p = p} Alphabet State ->
  List Alphabet ->
  State
eval automaton =
  evalFrom automaton (start automaton)

accepts :
  {a s p : Level} ->
  {Alphabet : Set a} ->
  {State : Set s} ->
  DFA {p = p} Alphabet State ->
  Language p Alphabet
accepts automaton word =
  accept automaton (eval automaton word)

record Regular
  {a p : Level}
  {Alphabet : Set a}
  (language : Language p Alphabet) :
  Set (a lmax lsuc p) where

  field
    State : Set
    finite-state : Finite State
    automaton : DFA {p = p} Alphabet State
    accepts-language :
      LanguageEquivalent
        (accepts automaton)
        language

record FiniteLeftQuotientRange
  {a p : Level}
  {Alphabet : Set a}
  (language : Language p Alphabet) :
  Set (a lmax lsuc p) where

  field
    QuotientIndex : Set
    finite-index : Finite QuotientIndex
    representative :
      QuotientIndex ->
      Language p Alphabet
    covers-quotients :
      (prefix : List Alphabet) ->
      Σ QuotientIndex
        (\ index ->
          LanguageEquivalent
            (leftQuotient language prefix)
            (representative index))
    representatives-are-quotients :
      (index : QuotientIndex) ->
      Σ (List Alphabet)
        (\ prefix ->
          LanguageEquivalent
            (representative index)
            (leftQuotient language prefix))

MyhillNerodeTheorem :
  {a p : Level} ->
  Set (lsuc (a lmax p))
MyhillNerodeTheorem {a} {p} =
  (Alphabet : Set a) ->
  (language : Language p Alphabet) ->
  (Regular language) iff
  (FiniteLeftQuotientRange language)
