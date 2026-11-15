-- Statement-only formalization of "The Ballot Problem" from Hundred Theorems item 030.
-- It counts fixed A/B vote sequences and those in which A stays strictly ahead at every prefix.
-- This file contains no proof.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<_
infixr 5 _++_
infixr 6 _and_

data _<_ : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} →
    zero < suc n
  successor-less-successor :
    {m n : Nat} →
    m < n →
    suc m < suc n

data Vote : Set where
  A B : Vote

_and_ : Bool → Bool → Bool
true and condition = condition
false and condition = false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

lessThan : Nat → Nat → Bool
lessThan zero zero = false
lessThan zero (suc n) = true
lessThan (suc m) zero = false
lessThan (suc m) (suc n) = lessThan m n

_++_ : {X : Set} → List X → List X → List X
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

mapList :
  {X Y : Set} →
  (X → Y) →
  List X →
  List Y
mapList function [] = []
mapList function (x ∷ xs) =
  function x ∷ mapList function xs

prependA : List Vote → List Vote
prependA votes = A ∷ votes

prependB : List Vote → List Vote
prependB votes = B ∷ votes

allVoteSequences : Nat → List (List Vote)
allVoteSequences zero = [] ∷ []
allVoteSequences (suc n) =
  mapList prependA (allVoteSequences n) ++
  mapList prependB (allVoteSequences n)

countA : List Vote → Nat
countA [] = zero
countA (A ∷ votes) = suc (countA votes)
countA (B ∷ votes) = countA votes

countB : List Vote → Nat
countB [] = zero
countB (A ∷ votes) = countB votes
countB (B ∷ votes) = suc (countB votes)

hasVoteCounts : Nat → Nat → List Vote → Bool
hasVoteCounts p q votes =
  natEqual (countA votes) p and
  natEqual (countB votes) q

staysAheadFrom : Nat → Nat → List Vote → Bool
staysAheadFrom a b [] = true
staysAheadFrom a b (A ∷ votes) =
  lessThan b (suc a) and
  staysAheadFrom (suc a) b votes
staysAheadFrom a b (B ∷ votes) =
  lessThan (suc b) a and
  staysAheadFrom a (suc b) votes

staysAhead : List Vote → Bool
staysAhead = staysAheadFrom zero zero

validSequence : Nat → Nat → List Vote → Bool
validSequence p q votes =
  hasVoteCounts p q votes and staysAhead votes

filterList :
  {X : Set} →
  (X → Bool) →
  List X →
  List X
filterList predicate [] = []
filterList predicate (x ∷ xs) with predicate x
... | true = x ∷ filterList predicate xs
... | false = filterList predicate xs

length : {X : Set} → List X → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

allCountings : Nat → Nat → Nat
allCountings p q =
  length
    (filterList
      (hasVoteCounts p q)
      (allVoteSequences (p + q)))

validCountings : Nat → Nat → Nat
validCountings p q =
  length
    (filterList
      (validSequence p q)
      (allVoteSequences (p + q)))

the-ballot-problem : Set
the-ballot-problem =
  (p q : Nat) →
  q < p →
  (p + q) * validCountings p q ≡
  (p - q) * allCountings p q
