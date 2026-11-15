-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_a3:
-- the universal assertion that every assignment of subsets of six courses to
-- twenty students admits five students and two courses such that all five
-- choose both courses or omit both courses is false. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Level; _⊔_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : {a : Level} -> Set a -> Set a
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
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
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one two three four five six : Nat
one =
  suc zero
two =
  suc one
three =
  suc two
four =
  suc three
five =
  suc four
six =
  suc five

seven eight nine ten eleven twelve thirteen fourteen fifteen : Nat
seven =
  suc six
eight =
  suc seven
nine =
  suc eight
ten =
  suc nine
eleven =
  suc ten
twelve =
  suc eleven
thirteen =
  suc twelve
fourteen =
  suc thirteen
fifteen =
  suc fourteen

sixteen seventeen eighteen nineteen twenty : Nat
sixteen =
  suc fifteen
seventeen =
  suc sixteen
eighteen =
  suc seventeen
nineteen =
  suc eighteen
twenty =
  suc nineteen

Student : Set
Student =
  Fin twenty

Course : Set
Course =
  Fin six

ChoiceAssignment : Set1
ChoiceAssignment =
  Student -> Course -> Set

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A} function =
  (x y : A) ->
  function x == function y ->
  x == y

AllChosen :
  ChoiceAssignment ->
  (Fin five -> Student) ->
  (Fin two -> Course) ->
  Set
AllChosen choices students courses =
  (student-index : Fin five) ->
  (course-index : Fin two) ->
  choices
    (students student-index)
    (courses course-index)

AllOmitted :
  ChoiceAssignment ->
  (Fin five -> Student) ->
  (Fin two -> Course) ->
  Set
AllOmitted choices students courses =
  (student-index : Fin five) ->
  (course-index : Fin two) ->
  Not
    (choices
      (students student-index)
      (courses course-index))

SelectionPrinciple : Set1
SelectionPrinciple =
  (choices : ChoiceAssignment) ->
  Exists (Fin five -> Student)
    (\ students ->
      Injective students
      and
      Exists (Fin two -> Course)
        (\ courses ->
          Injective courses
          and
          (AllChosen choices students courses
           or
           AllOmitted choices students courses)))

putnam-1996-a3-solution : Set
putnam-1996-a3-solution =
  Bottom

putnam-1996-a3 : Set1
putnam-1996-a3 =
  Iff SelectionPrinciple putnam-1996-a3-solution
