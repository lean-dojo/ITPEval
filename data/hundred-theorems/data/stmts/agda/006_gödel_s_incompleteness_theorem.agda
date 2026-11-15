-- Statement-only formalization of Hundred Theorems artifact 006, "Gödel's
-- Incompleteness Theorem": a weakly consistent theory extending the fixed
-- first-order arithmetic theory NN, whose axioms are represented in that
-- arithmetic, has a closed formula independent of the theory. This file
-- contains no proof.

module GoedelsIncompleteness where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 4 _or_
infixr 5 _and_
infixr 6 _++_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

natEqual : Nat -> Nat -> Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natMaximum : Nat -> Nat -> Nat
natMaximum zero n = n
natMaximum m zero = m
natMaximum (suc m) (suc n) = suc (natMaximum m n)

boolOr : Bool -> Bool -> Bool
boolOr false value = value
boolOr true _ = true

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ rightList = rightList
(head ∷ tail) ++ rightList = head ∷ (tail ++ rightList)

data Member {A : Set} (value : A) : List A -> Set where
  here  : {tail : List A} -> Member value (value ∷ tail)
  there : {head : A} {tail : List A} ->
    Member value tail ->
    Member value (head ∷ tail)

-- Terms and formulas in the first-order language of arithmetic.
data Term : Set where
  termVariable : Nat -> Term
  termZero      : Term
  termSuccessor : Term -> Term
  termAdd       : Term -> Term -> Term
  termMultiply  : Term -> Term -> Term

data Formula : Set where
  formulaEqual   : Term -> Term -> Formula
  formulaLess    : Term -> Term -> Formula
  formulaImplies : Formula -> Formula -> Formula
  formulaNegate  : Formula -> Formula
  formulaForall  : Nat -> Formula -> Formula

Theory : Set₁
Theory = Formula -> Set

formulaDisjunction : Formula -> Formula -> Formula
formulaDisjunction leftFormula rightFormula =
  formulaImplies (formulaNegate leftFormula) rightFormula

formulaConjunction : Formula -> Formula -> Formula
formulaConjunction leftFormula rightFormula =
  formulaNegate
    (formulaImplies leftFormula (formulaNegate rightFormula))

formulaBiconditional : Formula -> Formula -> Formula
formulaBiconditional leftFormula rightFormula =
  formulaConjunction
    (formulaImplies leftFormula rightFormula)
    (formulaImplies rightFormula leftFormula)

formulaExists : Nat -> Formula -> Formula
formulaExists index body =
  formulaNegate (formulaForall index (formulaNegate body))

termFreeVariable : Term -> Nat -> Set
termFreeVariable (termVariable index) free = index == free
termFreeVariable termZero free = Bottom
termFreeVariable (termSuccessor term) free =
  termFreeVariable term free
termFreeVariable (termAdd leftTerm rightTerm) free =
  termFreeVariable leftTerm free or termFreeVariable rightTerm free
termFreeVariable (termMultiply leftTerm rightTerm) free =
  termFreeVariable leftTerm free or termFreeVariable rightTerm free

formulaFreeVariable : Formula -> Nat -> Set
formulaFreeVariable (formulaEqual leftTerm rightTerm) free =
  termFreeVariable leftTerm free or termFreeVariable rightTerm free
formulaFreeVariable (formulaLess leftTerm rightTerm) free =
  termFreeVariable leftTerm free or termFreeVariable rightTerm free
formulaFreeVariable (formulaImplies leftFormula rightFormula) free =
  formulaFreeVariable leftFormula free or
  formulaFreeVariable rightFormula free
formulaFreeVariable (formulaNegate body) free =
  formulaFreeVariable body free
formulaFreeVariable (formulaForall bound body) free =
  Not (free == bound) and formulaFreeVariable body free

termHasVariable : Term -> Nat -> Bool
termHasVariable (termVariable index) sought = natEqual index sought
termHasVariable termZero sought = false
termHasVariable (termSuccessor term) sought =
  termHasVariable term sought
termHasVariable (termAdd leftTerm rightTerm) sought =
  boolOr
    (termHasVariable leftTerm sought)
    (termHasVariable rightTerm sought)
termHasVariable (termMultiply leftTerm rightTerm) sought =
  boolOr
    (termHasVariable leftTerm sought)
    (termHasVariable rightTerm sought)

termMaximumVariable : Term -> Nat
termMaximumVariable (termVariable index) = index
termMaximumVariable termZero = zero
termMaximumVariable (termSuccessor term) = termMaximumVariable term
termMaximumVariable (termAdd leftTerm rightTerm) =
  natMaximum
    (termMaximumVariable leftTerm)
    (termMaximumVariable rightTerm)
termMaximumVariable (termMultiply leftTerm rightTerm) =
  natMaximum
    (termMaximumVariable leftTerm)
    (termMaximumVariable rightTerm)

formulaMaximumVariable : Formula -> Nat
formulaMaximumVariable (formulaEqual leftTerm rightTerm) =
  natMaximum
    (termMaximumVariable leftTerm)
    (termMaximumVariable rightTerm)
formulaMaximumVariable (formulaLess leftTerm rightTerm) =
  natMaximum
    (termMaximumVariable leftTerm)
    (termMaximumVariable rightTerm)
formulaMaximumVariable (formulaImplies leftFormula rightFormula) =
  natMaximum
    (formulaMaximumVariable leftFormula)
    (formulaMaximumVariable rightFormula)
formulaMaximumVariable (formulaNegate body) =
  formulaMaximumVariable body
formulaMaximumVariable (formulaForall bound body) =
  natMaximum bound (formulaMaximumVariable body)

termRename : Nat -> Nat -> Term -> Term
termRename old fresh (termVariable index) with natEqual index old
... | true = termVariable fresh
... | false = termVariable index
termRename old fresh termZero = termZero
termRename old fresh (termSuccessor term) =
  termSuccessor (termRename old fresh term)
termRename old fresh (termAdd leftTerm rightTerm) =
  termAdd
    (termRename old fresh leftTerm)
    (termRename old fresh rightTerm)
termRename old fresh (termMultiply leftTerm rightTerm) =
  termMultiply
    (termRename old fresh leftTerm)
    (termRename old fresh rightTerm)

-- Rename occurrences governed by an outer binder, stopping at shadowing
-- quantifiers with the same variable name.
formulaRenameBound : Nat -> Nat -> Formula -> Formula
formulaRenameBound old fresh (formulaEqual leftTerm rightTerm) =
  formulaEqual
    (termRename old fresh leftTerm)
    (termRename old fresh rightTerm)
formulaRenameBound old fresh (formulaLess leftTerm rightTerm) =
  formulaLess
    (termRename old fresh leftTerm)
    (termRename old fresh rightTerm)
formulaRenameBound old fresh
  (formulaImplies leftFormula rightFormula) =
  formulaImplies
    (formulaRenameBound old fresh leftFormula)
    (formulaRenameBound old fresh rightFormula)
formulaRenameBound old fresh (formulaNegate body) =
  formulaNegate (formulaRenameBound old fresh body)
formulaRenameBound old fresh (formulaForall bound body)
  with natEqual bound old
... | true = formulaForall bound body
... | false =
  formulaForall bound (formulaRenameBound old fresh body)

formulaDepth : Formula -> Nat
formulaDepth (formulaEqual _ _) = suc zero
formulaDepth (formulaLess _ _) = suc zero
formulaDepth (formulaImplies leftFormula rightFormula) =
  suc
    (natMaximum
      (formulaDepth leftFormula)
      (formulaDepth rightFormula))
formulaDepth (formulaNegate body) = suc (formulaDepth body)
formulaDepth (formulaForall _ body) = suc (formulaDepth body)

termSubstitute : Term -> Nat -> Term -> Term
termSubstitute (termVariable termIndex) index replacement
  with natEqual termIndex index
... | true = replacement
... | false = termVariable termIndex
termSubstitute termZero index replacement = termZero
termSubstitute (termSuccessor term) index replacement =
  termSuccessor (termSubstitute term index replacement)
termSubstitute (termAdd leftTerm rightTerm) index replacement =
  termAdd
    (termSubstitute leftTerm index replacement)
    (termSubstitute rightTerm index replacement)
termSubstitute (termMultiply leftTerm rightTerm) index replacement =
  termMultiply
    (termSubstitute leftTerm index replacement)
    (termSubstitute rightTerm index replacement)

-- Fuel-bounded capture-avoiding substitution for the fixed syntax.
formulaSubstituteFuel :
  Nat ->
  Formula ->
  Nat ->
  Term ->
  Formula
formulaSubstituteFuel zero formula index replacement = formula
formulaSubstituteFuel (suc fuel)
  (formulaEqual leftTerm rightTerm) index replacement =
  formulaEqual
    (termSubstitute leftTerm index replacement)
    (termSubstitute rightTerm index replacement)
formulaSubstituteFuel (suc fuel)
  (formulaLess leftTerm rightTerm) index replacement =
  formulaLess
    (termSubstitute leftTerm index replacement)
    (termSubstitute rightTerm index replacement)
formulaSubstituteFuel (suc fuel)
  (formulaImplies leftFormula rightFormula) index replacement =
  formulaImplies
    (formulaSubstituteFuel fuel leftFormula index replacement)
    (formulaSubstituteFuel fuel rightFormula index replacement)
formulaSubstituteFuel (suc fuel)
  (formulaNegate body) index replacement =
  formulaNegate
    (formulaSubstituteFuel fuel body index replacement)
formulaSubstituteFuel (suc fuel)
  (formulaForall bound body) index replacement
  with natEqual bound index
... | true = formulaForall bound body
... | false with termHasVariable replacement bound
...   | true =
  let fresh =
        suc
          (natMaximum
            (formulaMaximumVariable body)
            (natMaximum
              (termMaximumVariable replacement)
              (natMaximum index bound)))
  in formulaForall fresh
       (formulaSubstituteFuel fuel
         (formulaRenameBound bound fresh body)
         index
         replacement)
...   | false =
  formulaForall bound
    (formulaSubstituteFuel fuel body index replacement)

formulaSubstitute : Formula -> Nat -> Term -> Formula
formulaSubstitute formula index replacement =
  formulaSubstituteFuel
    (formulaDepth formula)
    formula
    index
    replacement

termNumeral : Nat -> Term
termNumeral zero = termZero
termNumeral (suc n) = termSuccessor (termNumeral n)

natPower : Nat -> Nat -> Nat
natPower base zero = suc zero
natPower base (suc exponent) =
  base * natPower base exponent

pairCode : Nat -> Nat -> Nat
pairCode leftCode rightCode =
  natPower (suc (suc zero)) leftCode *
  (suc (suc zero) * rightCode + suc zero)

termCode : Term -> Nat
termCode (termVariable index) =
  suc (suc (suc (suc (suc zero)))) * index
termCode termZero = suc zero
termCode (termSuccessor term) =
  suc (suc (suc (suc (suc zero)))) * termCode term +
  suc (suc zero)
termCode (termAdd leftTerm rightTerm) =
  suc (suc (suc (suc (suc zero)))) *
  pairCode (termCode leftTerm) (termCode rightTerm) +
  suc (suc (suc zero))
termCode (termMultiply leftTerm rightTerm) =
  suc (suc (suc (suc (suc zero)))) *
  pairCode (termCode leftTerm) (termCode rightTerm) +
  suc (suc (suc (suc zero)))

formulaCode : Formula -> Nat
formulaCode (formulaEqual leftTerm rightTerm) =
  suc (suc (suc (suc (suc zero)))) *
  pairCode (termCode leftTerm) (termCode rightTerm)
formulaCode (formulaLess leftTerm rightTerm) =
  suc (suc (suc (suc (suc zero)))) *
  pairCode (termCode leftTerm) (termCode rightTerm) +
  suc zero
formulaCode (formulaImplies leftFormula rightFormula) =
  suc (suc (suc (suc (suc zero)))) *
  pairCode (formulaCode leftFormula) (formulaCode rightFormula) +
  suc (suc zero)
formulaCode (formulaNegate body) =
  suc (suc (suc (suc (suc zero)))) * formulaCode body +
  suc (suc (suc zero))
formulaCode (formulaForall bound body) =
  suc (suc (suc (suc (suc zero)))) *
  pairCode bound (formulaCode body) +
  suc (suc (suc (suc zero)))

formulaReflection : Formula -> Term
formulaReflection formula = termNumeral (formulaCode formula)

-- A concrete Hilbert derivation calculus for first-order arithmetic.
data Derivation : List Formula -> Formula -> Set where
  assumption :
    (formula : Formula) ->
    Derivation (formula ∷ []) formula
  modusPonens :
    {leftHypotheses rightHypotheses : List Formula}
    {antecedent consequent : Formula} ->
    Derivation
      leftHypotheses
      (formulaImplies antecedent consequent) ->
    Derivation rightHypotheses antecedent ->
    Derivation
      (leftHypotheses ++ rightHypotheses)
      consequent
  generalize :
    {hypotheses : List Formula}
    {formula : Formula}
    {index : Nat} ->
    ((hypothesis : Formula) ->
      Member hypothesis hypotheses ->
      Not (formulaFreeVariable hypothesis index)) ->
    Derivation hypotheses formula ->
    Derivation hypotheses (formulaForall index formula)
  implicationOne :
    (leftFormula rightFormula : Formula) ->
    Derivation []
      (formulaImplies leftFormula
        (formulaImplies rightFormula leftFormula))
  implicationTwo :
    (leftFormula middleFormula rightFormula : Formula) ->
    Derivation []
      (formulaImplies
        (formulaImplies leftFormula
          (formulaImplies middleFormula rightFormula))
        (formulaImplies
          (formulaImplies leftFormula middleFormula)
          (formulaImplies leftFormula rightFormula)))
  contraposition :
    (leftFormula rightFormula : Formula) ->
    Derivation []
      (formulaImplies
        (formulaImplies
          (formulaNegate leftFormula)
          (formulaNegate rightFormula))
        (formulaImplies rightFormula leftFormula))
  forallElimination :
    (formula : Formula) ->
    (index : Nat) ->
    (term : Term) ->
    Derivation []
      (formulaImplies
        (formulaForall index formula)
        (formulaSubstitute formula index term))
  forallIntroduction :
    (formula : Formula) ->
    (index : Nat) ->
    Not (formulaFreeVariable formula index) ->
    Derivation []
      (formulaImplies formula (formulaForall index formula))
  forallImplication :
    (leftFormula rightFormula : Formula) ->
    (index : Nat) ->
    Derivation []
      (formulaImplies
        (formulaForall index
          (formulaImplies leftFormula rightFormula))
        (formulaImplies
          (formulaForall index leftFormula)
          (formulaForall index rightFormula)))
  equalityReflexive :
    Derivation []
      (formulaEqual (termVariable zero) (termVariable zero))
  equalitySymmetric :
    Derivation []
      (formulaImplies
        (formulaEqual
          (termVariable zero)
          (termVariable (suc zero)))
        (formulaEqual
          (termVariable (suc zero))
          (termVariable zero)))
  equalityTransitive :
    Derivation []
      (formulaImplies
        (formulaEqual
          (termVariable zero)
          (termVariable (suc zero)))
        (formulaImplies
          (formulaEqual
            (termVariable (suc zero))
            (termVariable (suc (suc zero))))
          (formulaEqual
            (termVariable zero)
            (termVariable (suc (suc zero))))))
  lessCongruence :
    Derivation []
      (formulaImplies
        (formulaEqual
          (termVariable zero)
          (termVariable (suc zero)))
        (formulaImplies
          (formulaEqual
            (termVariable (suc (suc zero)))
            (termVariable (suc (suc (suc zero)))))
          (formulaBiconditional
            (formulaLess
              (termVariable zero)
              (termVariable (suc (suc zero))))
            (formulaLess
              (termVariable (suc zero))
              (termVariable (suc (suc (suc zero))))))))
  successorCongruence :
    Derivation []
      (formulaImplies
        (formulaEqual
          (termVariable zero)
          (termVariable (suc zero)))
        (formulaEqual
          (termSuccessor (termVariable zero))
          (termSuccessor (termVariable (suc zero)))))
  additionCongruence :
    Derivation []
      (formulaImplies
        (formulaEqual
          (termVariable zero)
          (termVariable (suc zero)))
        (formulaImplies
          (formulaEqual
            (termVariable (suc (suc zero)))
            (termVariable (suc (suc (suc zero)))))
          (formulaEqual
            (termAdd
              (termVariable zero)
              (termVariable (suc (suc zero))))
            (termAdd
              (termVariable (suc zero))
              (termVariable (suc (suc (suc zero))))))))
  multiplicationCongruence :
    Derivation []
      (formulaImplies
        (formulaEqual
          (termVariable zero)
          (termVariable (suc zero)))
        (formulaImplies
          (formulaEqual
            (termVariable (suc (suc zero)))
            (termVariable (suc (suc (suc zero)))))
          (formulaEqual
            (termMultiply
              (termVariable zero)
              (termVariable (suc (suc zero))))
            (termMultiply
              (termVariable (suc zero))
              (termVariable (suc (suc (suc zero))))))))

Provable : Theory -> Formula -> Set
Provable theory formula =
  Exists (List Formula)
    (\ hypotheses ->
      Derivation hypotheses formula and
      ((hypothesis : Formula) ->
        Member hypothesis hypotheses ->
        theory hypothesis))

Independent : Theory -> Formula -> Set
Independent theory formula =
  Not (Provable theory formula) and
  Not (Provable theory (formulaNegate formula))

Closed : Formula -> Set
Closed formula =
  (index : Nat) -> Not (formulaFreeVariable formula index)

-- The source's omega-consistency condition: if the theory proves an
-- existential counterexample to a one-variable formula, some numeral
-- instance of that formula is unprovable.
WeaklyConsistent : Theory -> Set
WeaklyConsistent theory =
  (formula : Formula) ->
  (index : Nat) ->
  ((free : Nat) ->
    formulaFreeVariable formula free ->
    index == free) ->
  Provable theory
    (formulaExists index (formulaNegate formula)) ->
  Exists Nat
    (\ number ->
      Not
        (Provable theory
          (formulaSubstitute
            formula
            index
            (termNumeral number))))

nn1 : Formula
nn1 =
  formulaForall zero
    (formulaNegate
      (formulaEqual
        (termSuccessor (termVariable zero))
        termZero))

nn2 : Formula
nn2 =
  formulaForall (suc zero)
    (formulaForall zero
      (formulaImplies
        (formulaEqual
          (termSuccessor (termVariable zero))
          (termSuccessor (termVariable (suc zero))))
        (formulaEqual
          (termVariable zero)
          (termVariable (suc zero)))))

nn3 : Formula
nn3 =
  formulaForall zero
    (formulaEqual
      (termAdd (termVariable zero) termZero)
      (termVariable zero))

nn4 : Formula
nn4 =
  formulaForall (suc zero)
    (formulaForall zero
      (formulaEqual
        (termAdd
          (termVariable zero)
          (termSuccessor (termVariable (suc zero))))
        (termSuccessor
          (termAdd
            (termVariable zero)
            (termVariable (suc zero))))))

nn5 : Formula
nn5 =
  formulaForall zero
    (formulaEqual
      (termMultiply (termVariable zero) termZero)
      termZero)

nn6 : Formula
nn6 =
  formulaForall (suc zero)
    (formulaForall zero
      (formulaEqual
        (termMultiply
          (termVariable zero)
          (termSuccessor (termVariable (suc zero))))
        (termAdd
          (termMultiply
            (termVariable zero)
            (termVariable (suc zero)))
          (termVariable zero))))

nn7 : Formula
nn7 =
  formulaForall zero
    (formulaNegate
      (formulaLess (termVariable zero) termZero))

nn8 : Formula
nn8 =
  formulaForall (suc zero)
    (formulaForall zero
      (formulaImplies
        (formulaLess
          (termVariable zero)
          (termSuccessor (termVariable (suc zero))))
        (formulaDisjunction
          (formulaLess
            (termVariable zero)
            (termVariable (suc zero)))
          (formulaEqual
            (termVariable zero)
            (termVariable (suc zero))))))

nn9 : Formula
nn9 =
  formulaForall (suc zero)
    (formulaForall zero
      (formulaDisjunction
        (formulaLess
          (termVariable zero)
          (termVariable (suc zero)))
        (formulaDisjunction
          (formulaEqual
            (termVariable zero)
            (termVariable (suc zero)))
          (formulaLess
            (termVariable (suc zero))
            (termVariable zero)))))

-- The fixed nine-axiom arithmetic theory NN used by the source.
NN : Theory
NN formula =
  (formula == nn1) or
  ((formula == nn2) or
  ((formula == nn3) or
  ((formula == nn4) or
  ((formula == nn5) or
  ((formula == nn6) or
  ((formula == nn7) or
  ((formula == nn8) or
   (formula == nn9))))))))

Extends : Theory -> Theory -> Set
Extends smaller larger =
  (formula : Formula) -> smaller formula -> larger formula

goedels-first-incompleteness-theorem : Set₁
goedels-first-incompleteness-theorem =
  (theory : Theory) ->
  Extends NN theory ->
  (representsTheory : Formula) ->
  (codeVariable : Nat) ->
  ((other : Nat) ->
    formulaFreeVariable representsTheory other ->
    other == codeVariable) ->
  ((formula : Formula) ->
    theory formula ->
    Provable theory
      (formulaSubstitute
        representsTheory
        codeVariable
        (formulaReflection formula))) ->
  ((formula : Formula) ->
    Not (theory formula) ->
    Provable theory
      (formulaNegate
        (formulaSubstitute
          representsTheory
          codeVariable
          (formulaReflection formula)))) ->
  WeaklyConsistent theory ->
  Exists Formula
    (\ formula ->
      Independent theory formula and Closed formula)
