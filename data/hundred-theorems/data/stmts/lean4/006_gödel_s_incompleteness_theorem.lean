-- Statement-only formalization of Hundred Theorems artifact 006, "Gödel's
-- Incompleteness Theorem": a weakly consistent theory extending the fixed
-- first-order arithmetic theory NN, whose axioms are represented in that
-- arithmetic, has a closed formula independent of the theory. This file
-- contains no proof.

namespace GoedelsIncompleteness

/-- Terms in the first-order language of arithmetic. -/
inductive Term where
  | var : Nat → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
deriving DecidableEq

/-- Formulas in the first-order language with equality and strict order. -/
inductive Formula where
  | equal : Term → Term → Formula
  | less : Term → Term → Formula
  | imp : Formula → Formula → Formula
  | neg : Formula → Formula
  | all : Nat → Formula → Formula
deriving DecidableEq

abbrev Theory := Formula → Prop

def Formula.disj (left right : Formula) : Formula :=
  Formula.imp (Formula.neg left) right

def Formula.conj (left right : Formula) : Formula :=
  Formula.neg (Formula.imp left (Formula.neg right))

def Formula.iffFormula (left right : Formula) : Formula :=
  Formula.conj (Formula.imp left right) (Formula.imp right left)

def Formula.existsFormula (index : Nat) (body : Formula) : Formula :=
  Formula.neg (Formula.all index (Formula.neg body))

def Term.freeVariable : Term → Nat → Prop
  | .var index, free => index = free
  | .zero, _ => False
  | .succ term, free => term.freeVariable free
  | .add left right, free =>
      left.freeVariable free ∨ right.freeVariable free
  | .mul left right, free =>
      left.freeVariable free ∨ right.freeVariable free

def Term.hasVariable : Term → Nat → Bool
  | .var index, sought => index == sought
  | .zero, _ => false
  | .succ term, sought => term.hasVariable sought
  | .add left right, sought =>
      left.hasVariable sought || right.hasVariable sought
  | .mul left right, sought =>
      left.hasVariable sought || right.hasVariable sought

def Formula.freeVariable : Formula → Nat → Prop
  | .equal left right, free =>
      left.freeVariable free ∨ right.freeVariable free
  | .less left right, free =>
      left.freeVariable free ∨ right.freeVariable free
  | .imp left right, free =>
      left.freeVariable free ∨ right.freeVariable free
  | .neg body, free => body.freeVariable free
  | .all bound body, free =>
      free ≠ bound ∧ body.freeVariable free

def Term.maxVariable : Term → Nat
  | .var index => index
  | .zero => 0
  | .succ term => term.maxVariable
  | .add left right => max left.maxVariable right.maxVariable
  | .mul left right => max left.maxVariable right.maxVariable

def Formula.maxVariable : Formula → Nat
  | .equal left right => max left.maxVariable right.maxVariable
  | .less left right => max left.maxVariable right.maxVariable
  | .imp left right => max left.maxVariable right.maxVariable
  | .neg body => body.maxVariable
  | .all bound body => max bound body.maxVariable

def Term.rename (old fresh : Nat) : Term → Term
  | .var index => .var (if index = old then fresh else index)
  | .zero => .zero
  | .succ term => .succ (term.rename old fresh)
  | .add left right =>
      .add (left.rename old fresh) (right.rename old fresh)
  | .mul left right =>
      .mul (left.rename old fresh) (right.rename old fresh)

def Formula.renameBound (old fresh : Nat) : Formula → Formula
  | .equal left right => .equal (left.rename old fresh) (right.rename old fresh)
  | .less left right => .less (left.rename old fresh) (right.rename old fresh)
  | .imp left right =>
      .imp (left.renameBound old fresh) (right.renameBound old fresh)
  | .neg body => .neg (body.renameBound old fresh)
  | .all bound body =>
      if bound = old then .all bound body
      else .all bound (body.renameBound old fresh)

def Formula.depth : Formula → Nat
  | .equal _ _ => 1
  | .less _ _ => 1
  | .imp left right => max left.depth right.depth + 1
  | .neg body => body.depth + 1
  | .all _ body => body.depth + 1

def Term.substitute (term : Term) (index : Nat) (replacement : Term) : Term :=
  match term with
  | .var termIndex => if termIndex = index then replacement else .var termIndex
  | .zero => .zero
  | .succ argument => .succ (argument.substitute index replacement)
  | .add left right =>
      .add (left.substitute index replacement) (right.substitute index replacement)
  | .mul left right =>
      .mul (left.substitute index replacement) (right.substitute index replacement)

/-- Fuel-bounded capture-avoiding substitution for the fixed arithmetic syntax. -/
def Formula.substituteFuel : Nat → Formula → Nat → Term → Formula
  | 0, formula, _, _ => formula
  | _ + 1, .equal left right, index, replacement =>
      .equal
        (left.substitute index replacement)
        (right.substitute index replacement)
  | _ + 1, .less left right, index, replacement =>
      .less
        (left.substitute index replacement)
        (right.substitute index replacement)
  | fuel + 1, .imp left right, index, replacement =>
      .imp
        (left.substituteFuel fuel index replacement)
        (right.substituteFuel fuel index replacement)
  | fuel + 1, .neg body, index, replacement =>
      .neg (body.substituteFuel fuel index replacement)
  | fuel + 1, .all bound body, index, replacement =>
      if bound = index then
        .all bound body
      else if replacement.hasVariable bound then
        let fresh :=
          max body.maxVariable
            (max replacement.maxVariable (max index bound)) + 1
        .all fresh
          ((body.renameBound bound fresh).substituteFuel fuel index replacement)
      else
        .all bound (body.substituteFuel fuel index replacement)

def Formula.substitute (formula : Formula) (index : Nat) (replacement : Term) : Formula :=
  formula.substituteFuel formula.depth index replacement

def Term.numeral : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (numeral n)

/-- The pairing function used by the fixed Gödel numbering. -/
def pairCode (left right : Nat) : Nat :=
  2 ^ left * (2 * right + 1)

def Term.code : Term → Nat
  | .var index => 5 * index
  | .zero => 1
  | .succ term => 5 * term.code + 2
  | .add left right => 5 * pairCode left.code right.code + 3
  | .mul left right => 5 * pairCode left.code right.code + 4

def Formula.code : Formula → Nat
  | .equal left right => 5 * pairCode left.code right.code
  | .less left right => 5 * pairCode left.code right.code + 1
  | .imp left right => 5 * pairCode left.code right.code + 2
  | .neg body => 5 * body.code + 3
  | .all bound body => 5 * pairCode bound body.code + 4

def Formula.reflect (formula : Formula) : Term :=
  Term.numeral formula.code

/-- Hilbert derivations for the fixed first-order language of arithmetic. -/
inductive Derivation : List Formula → Formula → Prop
  | axiom (formula : Formula) :
      Derivation [formula] formula
  | modusPonens
      (leftHypotheses rightHypotheses : List Formula)
      (antecedent consequent : Formula) :
      Derivation leftHypotheses (.imp antecedent consequent) →
      Derivation rightHypotheses antecedent →
      Derivation (leftHypotheses ++ rightHypotheses) consequent
  | generalize
      (hypotheses : List Formula) (formula : Formula) (index : Nat) :
      (∀ hypothesis, hypothesis ∈ hypotheses →
        ¬hypothesis.freeVariable index) →
      Derivation hypotheses formula →
      Derivation hypotheses (.all index formula)
  | impOne (left right : Formula) :
      Derivation [] (.imp left (.imp right left))
  | impTwo (left middle right : Formula) :
      Derivation []
        (.imp
          (.imp left (.imp middle right))
          (.imp (.imp left middle) (.imp left right)))
  | contraposition (left right : Formula) :
      Derivation []
        (.imp
          (.imp (.neg left) (.neg right))
          (.imp right left))
  | forallElim (formula : Formula) (index : Nat) (term : Term) :
      Derivation []
        (.imp
          (.all index formula)
          (formula.substitute index term))
  | forallIntro (formula : Formula) (index : Nat) :
      ¬formula.freeVariable index →
      Derivation [] (.imp formula (.all index formula))
  | forallImp (left right : Formula) (index : Nat) :
      Derivation []
        (.imp
          (.all index (.imp left right))
          (.imp (.all index left) (.all index right)))
  | equalityRefl :
      Derivation [] (.equal (.var 0) (.var 0))
  | equalitySymm :
      Derivation []
        (.imp
          (.equal (.var 0) (.var 1))
          (.equal (.var 1) (.var 0)))
  | equalityTrans :
      Derivation []
        (.imp
          (.equal (.var 0) (.var 1))
          (.imp
            (.equal (.var 1) (.var 2))
            (.equal (.var 0) (.var 2))))
  | lessCongruence :
      Derivation []
        (.imp
          (.equal (.var 0) (.var 1))
          (.imp
            (.equal (.var 2) (.var 3))
            (Formula.iffFormula
              (.less (.var 0) (.var 2))
              (.less (.var 1) (.var 3)))))
  | zeroCongruence :
      Derivation [] (.equal .zero .zero)
  | succCongruence :
      Derivation []
        (.imp
          (.equal (.var 0) (.var 1))
          (.equal (.succ (.var 0)) (.succ (.var 1))))
  | addCongruence :
      Derivation []
        (.imp
          (.equal (.var 0) (.var 1))
          (.imp
            (.equal (.var 2) (.var 3))
            (.equal
              (.add (.var 0) (.var 2))
              (.add (.var 1) (.var 3)))))
  | mulCongruence :
      Derivation []
        (.imp
          (.equal (.var 0) (.var 1))
          (.imp
            (.equal (.var 2) (.var 3))
            (.equal
              (.mul (.var 0) (.var 2))
              (.mul (.var 1) (.var 3)))))

def Provable (theory : Theory) (formula : Formula) : Prop :=
  ∃ hypotheses : List Formula,
    Derivation hypotheses formula ∧
    ∀ hypothesis, hypothesis ∈ hypotheses → theory hypothesis

def Independent (theory : Theory) (formula : Formula) : Prop :=
  ¬Provable theory formula ∧ ¬Provable theory (.neg formula)

def Closed (formula : Formula) : Prop :=
  ∀ index, ¬formula.freeVariable index

/--
The source's ω-consistency condition: if the theory proves an existential
counterexample to a one-variable formula, some numeral instance is unprovable.
-/
def WeaklyConsistent (theory : Theory) : Prop :=
  ∀ formula index,
    (∀ free, formula.freeVariable free → index = free) →
    Provable theory (.existsFormula index (.neg formula)) →
    ∃ number : Nat,
      ¬Provable theory (formula.substitute index (Term.numeral number))

def nn1 : Formula :=
  .all 0 (.neg (.equal (.succ (.var 0)) .zero))

def nn2 : Formula :=
  .all 1 <| .all 0 <|
    .imp
      (.equal (.succ (.var 0)) (.succ (.var 1)))
      (.equal (.var 0) (.var 1))

def nn3 : Formula :=
  .all 0 (.equal (.add (.var 0) .zero) (.var 0))

def nn4 : Formula :=
  .all 1 <| .all 0 <|
    .equal
      (.add (.var 0) (.succ (.var 1)))
      (.succ (.add (.var 0) (.var 1)))

def nn5 : Formula :=
  .all 0 (.equal (.mul (.var 0) .zero) .zero)

def nn6 : Formula :=
  .all 1 <| .all 0 <|
    .equal
      (.mul (.var 0) (.succ (.var 1)))
      (.add (.mul (.var 0) (.var 1)) (.var 0))

def nn7 : Formula :=
  .all 0 (.neg (.less (.var 0) .zero))

def nn8 : Formula :=
  .all 1 <| .all 0 <|
    .imp
      (.less (.var 0) (.succ (.var 1)))
      (Formula.disj
        (.less (.var 0) (.var 1))
        (.equal (.var 0) (.var 1)))

def nn9 : Formula :=
  .all 1 <| .all 0 <|
    Formula.disj
      (.less (.var 0) (.var 1))
      (Formula.disj
        (.equal (.var 0) (.var 1))
        (.less (.var 1) (.var 0)))

/-- The fixed nine-axiom arithmetic theory `NN` used by the Rocq source. -/
def NN : Theory :=
  fun formula =>
    formula = nn1 ∨ formula = nn2 ∨ formula = nn3 ∨
    formula = nn4 ∨ formula = nn5 ∨ formula = nn6 ∨
    formula = nn7 ∨ formula = nn8 ∨ formula = nn9

/--
Gödel's first incompleteness theorem for the fixed arithmetic syntax,
Gödel numbering, derivability relation, and ω-consistency predicate above.
-/
theorem goedels_first_incompleteness
    (theory : Theory)
    (extendsNN : ∀ formula, NN formula → theory formula)
    (representsTheory : Formula)
    (codeVariable : Nat)
    (onlyFreeVariable :
      ∀ other, representsTheory.freeVariable other → other = codeVariable)
    (expressesMembership :
      ∀ formula, theory formula →
        Provable theory
          (representsTheory.substitute codeVariable formula.reflect))
    (expressesNonmembership :
      ∀ formula, ¬theory formula →
        Provable theory
          (.neg (representsTheory.substitute codeVariable formula.reflect)))
    (consistent : WeaklyConsistent theory) :
    ∃ formula : Formula, Independent theory formula ∧ Closed formula := sorry

end GoedelsIncompleteness
