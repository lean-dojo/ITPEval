-- Statement-only formalization of Thousand Theorems artifact Q574902
-- (thousand-theorems__lean4__Q574902), "Tarski's indefinability theorem":
-- no unary formula in the first-order language of ordered semirings defines
-- truth for every closed arithmetic sentence in the standard natural-number model.
-- This file contains no proof.

namespace Q574902

/-- Terms in the first-order language with `0`, `1`, addition, and multiplication. -/
inductive Term (variables : Nat) where
  | bvar : Fin variables → Term variables
  | zero : Term variables
  | one : Term variables
  | add : Term variables → Term variables → Term variables
  | mul : Term variables → Term variables → Term variables

/--
Formulas in negation-normal form for the first-order language of ordered
semirings. Bound variables use de Bruijn indices.
-/
inductive Formula : Nat → Type where
  | verum {variables : Nat} : Formula variables
  | falsum {variables : Nat} : Formula variables
  | eq {variables : Nat} : Term variables → Term variables → Formula variables
  | neq {variables : Nat} : Term variables → Term variables → Formula variables
  | lt {variables : Nat} : Term variables → Term variables → Formula variables
  | nlt {variables : Nat} : Term variables → Term variables → Formula variables
  | and {variables : Nat} : Formula variables → Formula variables → Formula variables
  | or {variables : Nat} : Formula variables → Formula variables → Formula variables
  | all {variables : Nat} : Formula (variables + 1) → Formula variables
  | exs {variables : Nat} : Formula (variables + 1) → Formula variables

namespace Term

/-- Rename the de Bruijn variables in a term. -/
def rename {source target : Nat} (ρ : Fin source → Fin target) :
    Term source → Term target
  | .bvar index => .bvar (ρ index)
  | .zero => .zero
  | .one => .one
  | .add left right => .add (rename ρ left) (rename ρ right)
  | .mul left right => .mul (rename ρ left) (rename ρ right)

/-- Simultaneously substitute terms for all de Bruijn variables. -/
def subst {source target : Nat} (replacement : Fin source → Term target) :
    Term source → Term target
  | .bvar index => replacement index
  | .zero => .zero
  | .one => .one
  | .add left right => .add (subst replacement left) (subst replacement right)
  | .mul left right => .mul (subst replacement left) (subst replacement right)

/-- Evaluate an arithmetic term in the standard natural-number structure. -/
def eval {variables : Nat} (assignment : Fin variables → Nat) :
    Term variables → Nat
  | .bvar index => assignment index
  | .zero => 0
  | .one => 1
  | .add left right => eval assignment left + eval assignment right
  | .mul left right => eval assignment left * eval assignment right

end Term

/-- Extend an assignment with the value of the newest de Bruijn variable. -/
def extendAssignment {variables : Nat} (value : Nat)
    (assignment : Fin variables → Nat) : Fin (variables + 1) → Nat :=
  Fin.cases value assignment

/-- Lift a simultaneous substitution through one quantifier. -/
def liftSubstitution {source target : Nat}
    (replacement : Fin source → Term target) :
    Fin (source + 1) → Term (target + 1) :=
  Fin.cases (.bvar 0) (fun index => (replacement index).rename Fin.succ)

namespace Formula

/-- Capture-avoiding simultaneous substitution of arithmetic terms. -/
def subst {source target : Nat} (replacement : Fin source → Term target) :
    Formula source → Formula target
  | .verum => .verum
  | .falsum => .falsum
  | .eq left right => .eq (left.subst replacement) (right.subst replacement)
  | .neq left right => .neq (left.subst replacement) (right.subst replacement)
  | .lt left right => .lt (left.subst replacement) (right.subst replacement)
  | .nlt left right => .nlt (left.subst replacement) (right.subst replacement)
  | .and left right => .and (subst replacement left) (subst replacement right)
  | .or left right => .or (subst replacement left) (subst replacement right)
  | .all body => .all (subst (liftSubstitution replacement) body)
  | .exs body => .exs (subst (liftSubstitution replacement) body)

/-- Tarski satisfaction in the standard natural-number structure. -/
def eval {variables : Nat} (assignment : Fin variables → Nat) :
    Formula variables → Prop
  | .verum => True
  | .falsum => False
  | .eq left right => left.eval assignment = right.eval assignment
  | .neq left right => left.eval assignment ≠ right.eval assignment
  | .lt left right => left.eval assignment < right.eval assignment
  | .nlt left right => ¬left.eval assignment < right.eval assignment
  | .and left right => eval assignment left ∧ eval assignment right
  | .or left right => eval assignment left ∨ eval assignment right
  | .all body => ∀ value : Nat, eval (extendAssignment value assignment) body
  | .exs body => ∃ value : Nat, eval (extendAssignment value assignment) body

end Formula

/-- Truth of a closed arithmetic sentence in the standard model of `Nat`. -/
def TrueInNat (sentence : Formula 0) : Prop :=
  sentence.eval Fin.elim0

/-- The source's numeral term: `0`, `1`, and then repeated addition of `1`. -/
def numeral : Nat → Term 0
  | 0 => .zero
  | 1 => .one
  | n + 2 => .add (numeral (n + 1)) .one

/-- Instantiate the sole free de Bruijn variable of a unary formula by a numeral. -/
def instantiate (predicate : Formula 1) (number : Nat) : Formula 0 :=
  predicate.subst (fun _ => numeral number)

/-- The natural-number pairing function used by the source Gödel coding. -/
def pair (left right : Nat) : Nat :=
  if left < right then right * right + left else left * left + left + right

/-- Coding of a two-entry vector by the source's iterated pairing convention. -/
def vectorCode₂ (first second : Nat) : Nat :=
  pair first (pair second 0 + 1) + 1

namespace Term

/-- The source Gödel code, specialized to ordered-semiring terms. -/
def code {variables : Nat} : Term variables → Nat
  | .bvar index => pair 0 index.val + 1
  | .zero => pair 2 (pair 0 (pair 0 0)) + 1
  | .one => pair 2 (pair 0 (pair 1 0)) + 1
  | .add left right =>
      pair 2 (pair 2 (pair 0 (vectorCode₂ left.code right.code))) + 1
  | .mul left right =>
      pair 2 (pair 2 (pair 1 (vectorCode₂ left.code right.code))) + 1

end Term

namespace Formula

/-- The source Gödel code, specialized to ordered-semiring formulas. -/
def code {variables : Nat} : Formula variables → Nat
  | .eq left right =>
      pair 0 (pair 2 (pair 0 (vectorCode₂ left.code right.code))) + 1
  | .neq left right =>
      pair 1 (pair 2 (pair 0 (vectorCode₂ left.code right.code))) + 1
  | .lt left right =>
      pair 0 (pair 2 (pair 1 (vectorCode₂ left.code right.code))) + 1
  | .nlt left right =>
      pair 1 (pair 2 (pair 1 (vectorCode₂ left.code right.code))) + 1
  | .verum => pair 2 0 + 1
  | .falsum => pair 3 0 + 1
  | .and left right => pair 4 (pair left.code right.code) + 1
  | .or left right => pair 5 (pair left.code right.code) + 1
  | .all body => pair 6 body.code + 1
  | .exs body => pair 7 body.code + 1

end Formula

/--
Tarski's undefinability theorem: no unary arithmetic formula agrees, on the
Gödel code of every sentence, with truth in the standard natural-number model.
-/
theorem undefinability_of_truth :
    ¬∃ truthPredicate : Formula 1, ∀ sentence : Formula 0,
      TrueInNat sentence ↔
        TrueInNat (instantiate truthPredicate sentence.code) := sorry

end Q574902
