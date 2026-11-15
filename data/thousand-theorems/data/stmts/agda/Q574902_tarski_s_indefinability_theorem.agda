-- Statement-only formalization of thousand-theorems corpus artifact Q574902
-- (thousand-theorems__agda__Q574902), "Tarski's indefinability theorem":
-- no unary formula of first-order arithmetic defines truth for every closed
-- arithmetic sentence in the standard natural-number model. This file contains no proof.

{-# OPTIONS --safe #-}

module Q574902_tarski_s_indefinability_theorem where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _iff_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

record _and_ (left right : Set) : Set where
  constructor both
  field
    first : left
    second : right

data _or_ (left right : Set) : Set where
  left-injection : left -> left or right
  right-injection : right -> left or right

record _iff_ (left right : Set) : Set where
  constructor equivalence
  field
    forward : left -> right
    backward : right -> left

record Exists (A : Set) (predicate : A -> Set) : Set where
  constructor witness
  field
    value : A
    property : predicate value

-- Fin n is the type of de Bruijn variables in an n-variable context.
data Fin : Nat -> Set where
  first-variable : {n : Nat} -> Fin (suc n)
  next-variable : {n : Nat} -> Fin n -> Fin (suc n)

-- Terms and formulas for the first-order language of ordered semirings.
data Term (variables : Nat) : Set where
  variable-term : Fin variables -> Term variables
  zero-term : Term variables
  one-term : Term variables
  add-term : Term variables -> Term variables -> Term variables
  multiply-term : Term variables -> Term variables -> Term variables

data Formula (variables : Nat) : Set where
  equal-formula :
    Term variables ->
    Term variables ->
    Formula variables
  less-formula :
    Term variables ->
    Term variables ->
    Formula variables
  false-formula : Formula variables
  conjunction :
    Formula variables ->
    Formula variables ->
    Formula variables
  disjunction :
    Formula variables ->
    Formula variables ->
    Formula variables
  implication :
    Formula variables ->
    Formula variables ->
    Formula variables
  negation :
    Formula variables ->
    Formula variables
  universal :
    Formula (suc variables) ->
    Formula variables
  existential :
    Formula (suc variables) ->
    Formula variables

Environment : Nat -> Set
Environment variables =
  Fin variables -> Nat

extend-environment :
  {variables : Nat} ->
  Environment variables ->
  Nat ->
  Environment (suc variables)
extend-environment environment value first-variable =
  value
extend-environment environment value (next-variable index) =
  environment index

evaluate-term :
  {variables : Nat} ->
  Term variables ->
  Environment variables ->
  Nat
evaluate-term (variable-term index) environment =
  environment index
evaluate-term zero-term environment =
  zero
evaluate-term one-term environment =
  suc zero
evaluate-term (add-term left right) environment =
  evaluate-term left environment + evaluate-term right environment
evaluate-term (multiply-term left right) environment =
  evaluate-term left environment * evaluate-term right environment

Satisfies :
  {variables : Nat} ->
  Formula variables ->
  Environment variables ->
  Set
Satisfies (equal-formula left right) environment =
  evaluate-term left environment == evaluate-term right environment
Satisfies (less-formula left right) environment =
  (evaluate-term left environment < evaluate-term right environment) == true
Satisfies false-formula environment =
  Bottom
Satisfies (conjunction left right) environment =
  Satisfies left environment and Satisfies right environment
Satisfies (disjunction left right) environment =
  Satisfies left environment or Satisfies right environment
Satisfies (implication left right) environment =
  Satisfies left environment -> Satisfies right environment
Satisfies (negation proposition) environment =
  Not (Satisfies proposition environment)
Satisfies (universal body) environment =
  (value : Nat) ->
  Satisfies body (extend-environment environment value)
Satisfies (existential body) environment =
  Exists Nat
    (\ value ->
      Satisfies body (extend-environment environment value))

empty-environment : Environment zero
empty-environment ()

TrueInStandardNaturals : Formula zero -> Set
TrueInStandardNaturals sentence =
  Satisfies sentence empty-environment

lift-renaming :
  {source target : Nat} ->
  (Fin source -> Fin target) ->
  Fin (suc source) ->
  Fin (suc target)
lift-renaming rho first-variable =
  first-variable
lift-renaming rho (next-variable index) =
  next-variable (rho index)

rename-term :
  {source target : Nat} ->
  (Fin source -> Fin target) ->
  Term source ->
  Term target
rename-term rho (variable-term index) =
  variable-term (rho index)
rename-term rho zero-term =
  zero-term
rename-term rho one-term =
  one-term
rename-term rho (add-term left right) =
  add-term
    (rename-term rho left)
    (rename-term rho right)
rename-term rho (multiply-term left right) =
  multiply-term
    (rename-term rho left)
    (rename-term rho right)

lift-substitution :
  {source target : Nat} ->
  (Fin source -> Term target) ->
  Fin (suc source) ->
  Term (suc target)
lift-substitution substitution first-variable =
  variable-term first-variable
lift-substitution substitution (next-variable index) =
  rename-term next-variable (substitution index)

substitute-term :
  {source target : Nat} ->
  (Fin source -> Term target) ->
  Term source ->
  Term target
substitute-term substitution (variable-term index) =
  substitution index
substitute-term substitution zero-term =
  zero-term
substitute-term substitution one-term =
  one-term
substitute-term substitution (add-term left right) =
  add-term
    (substitute-term substitution left)
    (substitute-term substitution right)
substitute-term substitution (multiply-term left right) =
  multiply-term
    (substitute-term substitution left)
    (substitute-term substitution right)

substitute-formula :
  {source target : Nat} ->
  (Fin source -> Term target) ->
  Formula source ->
  Formula target
substitute-formula substitution (equal-formula left right) =
  equal-formula
    (substitute-term substitution left)
    (substitute-term substitution right)
substitute-formula substitution (less-formula left right) =
  less-formula
    (substitute-term substitution left)
    (substitute-term substitution right)
substitute-formula substitution false-formula =
  false-formula
substitute-formula substitution (conjunction left right) =
  conjunction
    (substitute-formula substitution left)
    (substitute-formula substitution right)
substitute-formula substitution (disjunction left right) =
  disjunction
    (substitute-formula substitution left)
    (substitute-formula substitution right)
substitute-formula substitution (implication left right) =
  implication
    (substitute-formula substitution left)
    (substitute-formula substitution right)
substitute-formula substitution (negation proposition) =
  negation (substitute-formula substitution proposition)
substitute-formula substitution (universal body) =
  universal
    (substitute-formula (lift-substitution substitution) body)
substitute-formula substitution (existential body) =
  existential
    (substitute-formula (lift-substitution substitution) body)

numeral : Nat -> Term zero
numeral zero =
  zero-term
numeral (suc n) =
  add-term one-term (numeral n)

instantiate :
  Formula (suc zero) ->
  Nat ->
  Formula zero
instantiate unary-formula number =
  substitute-formula replacement unary-formula
  where
  replacement : Fin (suc zero) -> Term zero
  replacement first-variable =
    numeral number

-- A fixed computable Gödel numbering of the concrete syntax above.
pair-natural : Nat -> Nat -> Nat
pair-natural left right with left < right
... | true =
  right * right + left
... | false =
  left * left + left + right

fin-code :
  {variables : Nat} ->
  Fin variables ->
  Nat
fin-code first-variable =
  zero
fin-code (next-variable index) =
  suc (fin-code index)

term-code :
  {variables : Nat} ->
  Term variables ->
  Nat
term-code (variable-term index) =
  pair-natural 0 (fin-code index)
term-code zero-term =
  pair-natural 1 0
term-code one-term =
  pair-natural 2 0
term-code (add-term left right) =
  pair-natural 3
    (pair-natural (term-code left) (term-code right))
term-code (multiply-term left right) =
  pair-natural 4
    (pair-natural (term-code left) (term-code right))

formula-code :
  {variables : Nat} ->
  Formula variables ->
  Nat
formula-code (equal-formula left right) =
  pair-natural 0
    (pair-natural (term-code left) (term-code right))
formula-code (less-formula left right) =
  pair-natural 1
    (pair-natural (term-code left) (term-code right))
formula-code false-formula =
  pair-natural 2 0
formula-code (conjunction left right) =
  pair-natural 3
    (pair-natural (formula-code left) (formula-code right))
formula-code (disjunction left right) =
  pair-natural 4
    (pair-natural (formula-code left) (formula-code right))
formula-code (implication left right) =
  pair-natural 5
    (pair-natural (formula-code left) (formula-code right))
formula-code (negation proposition) =
  pair-natural 6 (formula-code proposition)
formula-code (universal body) =
  pair-natural 7 (formula-code body)
formula-code (existential body) =
  pair-natural 8 (formula-code body)

tarski-s-indefinability-theorem : Set
tarski-s-indefinability-theorem =
  Not
    (Exists
      (Formula (suc zero))
      (\ truth-formula ->
        (sentence : Formula zero) ->
        (TrueInStandardNaturals sentence) iff
        (TrueInStandardNaturals
          (instantiate truth-formula (formula-code sentence)))))
