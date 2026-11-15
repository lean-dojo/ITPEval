-- Statement-only formalization of "The Undecidability of the Continuum Hypothesis" from Hundred
-- Theorems item 024. It asserts a proper countable transitive ZF extension with the same ordinals,
-- preserving Choice when present. This file contains no proof.

namespace ContinuumHypothesisUndecidability

universe u

/--
An Aczel-style universe of well-founded sets. A set may be formed from any small
indexing type, providing the ambient set formation needed for forcing constructions.
-/
inductive PSet : Type (u + 1) where
  | mk (Index : Type u) (element : Index → PSet)

/-- Extensional equality of well-founded set trees. -/
def PSet.Equiv : PSet.{u} → PSet.{u} → Prop
  | .mk _ left, .mk _ right =>
      (∀ i, ∃ j, Equiv (left i) (right j)) ∧
        (∀ j, ∃ i, Equiv (left i) (right j))

/-- Membership in a well-founded set, modulo extensional equality. -/
def PSet.Mem (x : PSet.{u}) : PSet.{u} → Prop
  | .mk _ element => ∃ i, Equiv x (element i)

/-- First-order formulas in the language of set theory, using de Bruijn variables. -/
inductive Formula where
  | equal (left right : Nat)
  | member (left right : Nat)
  | falsum
  | conjunction (left right : Formula)
  | disjunction (left right : Formula)
  | implication (left right : Formula)
  | negation (body : Formula)
  | universal (body : Formula)
  | existential (body : Formula)

/-- Add a new value for de Bruijn variable zero and shift the previous assignment. -/
def extendAssignment (value : PSet) (assignment : Nat → PSet) : Nat → PSet
  | 0 => value
  | Nat.succ index => assignment index

/-- Tarski satisfaction for membership formulas, with quantifiers restricted to a model. -/
def satisfies (model : PSet) (assignment : Nat → PSet) : Formula → Prop
  | .equal left right => PSet.Equiv (assignment left) (assignment right)
  | .member left right => PSet.Mem (assignment left) (assignment right)
  | .falsum => False
  | .conjunction left right =>
      satisfies model assignment left ∧ satisfies model assignment right
  | .disjunction left right =>
      satisfies model assignment left ∨ satisfies model assignment right
  | .implication left right =>
      satisfies model assignment left → satisfies model assignment right
  | .negation body => ¬satisfies model assignment body
  | .universal body =>
      ∀ value, PSet.Mem value model →
        satisfies model (extendAssignment value assignment) body
  | .existential body =>
      ∃ value, PSet.Mem value model ∧
        satisfies model (extendAssignment value assignment) body

/-- Every value in an assignment is an element of the model. -/
def AssignmentIn (model : PSet) (assignment : Nat → PSet) : Prop :=
  ∀ index, PSet.Mem (assignment index) model

/-- Inclusion between two sets that serve as model domains. -/
def ModelSubset (M N : PSet) : Prop :=
  ∀ x, PSet.Mem x M → PSet.Mem x N

/-- A set is transitive when it contains every member of each of its elements. -/
def TransitiveSet (M : PSet) : Prop :=
  ∀ {x y}, PSet.Mem x M → PSet.Mem y x → PSet.Mem y M

/-- A von Neumann ordinal is a transitive set linearly ordered by membership. -/
def IsOrdinal (ordinal : PSet) : Prop :=
  TransitiveSet ordinal ∧
    ∀ {x y}, PSet.Mem x ordinal → PSet.Mem y ordinal →
      PSet.Mem x y ∨ PSet.Equiv x y ∨ PSet.Mem y x

/-- The elements of a set are in bijection with the natural numbers. -/
def EquinumerousWithNat (M : PSet) : Prop :=
  ∃ enumeration : Nat → PSet,
    (∀ n, PSet.Mem (enumeration n) M) ∧
      (∀ {m n}, PSet.Equiv (enumeration m) (enumeration n) → m = n) ∧
      (∀ x, PSet.Mem x M → ∃ n, PSet.Equiv (enumeration n) x)

/-- Extensionality as seen inside a model. -/
def ModelsExtensionality (M : PSet) : Prop :=
  ∀ {x y}, PSet.Mem x M → PSet.Mem y M →
    (∀ z, PSet.Mem z M → (PSet.Mem z x ↔ PSet.Mem z y)) →
    PSet.Equiv x y

/-- The model contains an empty set. -/
def ModelsEmptySet (M : PSet) : Prop :=
  ∃ empty, PSet.Mem empty M ∧
    ∀ x, PSet.Mem x M → ¬PSet.Mem x empty

/-- The model is closed under unordered pairs. -/
def ModelsPairing (M : PSet) : Prop :=
  ∀ x, PSet.Mem x M →
    ∀ y, PSet.Mem y M →
      ∃ pair, PSet.Mem pair M ∧
        ∀ z, PSet.Mem z M →
          (PSet.Mem z pair ↔ PSet.Equiv z x ∨ PSet.Equiv z y)

/-- The model is closed under unions. -/
def ModelsUnion (M : PSet) : Prop :=
  ∀ family, PSet.Mem family M →
    ∃ union, PSet.Mem union M ∧
      ∀ x, PSet.Mem x M →
        (PSet.Mem x union ↔
          ∃ member, PSet.Mem member M ∧
            PSet.Mem member family ∧ PSet.Mem x member)

/-- Internal subsethood in a model. -/
def InternalSubset (M left right : PSet) : Prop :=
  ∀ x, PSet.Mem x M → PSet.Mem x left → PSet.Mem x right

/-- The model is closed under power sets. -/
def ModelsPowerSet (M : PSet) : Prop :=
  ∀ base, PSet.Mem base M →
    ∃ power, PSet.Mem power M ∧
      ∀ candidate, PSet.Mem candidate M →
        (PSet.Mem candidate power ↔ InternalSubset M candidate base)

/-- A set is empty according to the model. -/
def IsEmptyIn (M empty : PSet) : Prop :=
  PSet.Mem empty M ∧
    ∀ x, PSet.Mem x M → ¬PSet.Mem x empty

/-- `successor` is `x ∪ {x}` according to the model. -/
def IsSuccessorIn (M x successor : PSet) : Prop :=
  PSet.Mem successor M ∧
    ∀ z, PSet.Mem z M →
      (PSet.Mem z successor ↔ PSet.Mem z x ∨ PSet.Equiv z x)

/-- The model contains an inductive set. -/
def ModelsInfinity (M : PSet) : Prop :=
  ∃ infinity, PSet.Mem infinity M ∧
    ∃ empty, IsEmptyIn M empty ∧ PSet.Mem empty infinity ∧
      ∀ x, PSet.Mem x M → PSet.Mem x infinity →
        ∃ successor, IsSuccessorIn M x successor ∧ PSet.Mem successor infinity

/-- Every definable subclass of a set is represented by a set in the model. -/
def ModelsSeparation (M : PSet) : Prop :=
  ∀ formula assignment, AssignmentIn M assignment →
    ∀ base, PSet.Mem base M →
      ∃ subset, PSet.Mem subset M ∧
        ∀ x, PSet.Mem x M →
          (PSet.Mem x subset ↔
            PSet.Mem x base ∧
              satisfies M (extendAssignment x assignment) formula)

/-- Every definable functional image of a set is represented by a set in the model. -/
def ModelsReplacement (M : PSet) : Prop :=
  ∀ formula assignment, AssignmentIn M assignment →
    ∀ domain, PSet.Mem domain M →
      (∀ x, PSet.Mem x M → PSet.Mem x domain →
        ∃ y, PSet.Mem y M ∧
          satisfies M (extendAssignment y (extendAssignment x assignment)) formula ∧
          ∀ z, PSet.Mem z M →
            satisfies M
              (extendAssignment z (extendAssignment x assignment)) formula →
            PSet.Equiv z y) →
      ∃ range, PSet.Mem range M ∧
        ∀ y, PSet.Mem y M →
          (PSet.Mem y range ↔
            ∃ x, PSet.Mem x M ∧ PSet.Mem x domain ∧
              satisfies M
                (extendAssignment y (extendAssignment x assignment)) formula)

/-- Foundation as seen inside a model. -/
def ModelsFoundation (M : PSet) : Prop :=
  ∀ set, PSet.Mem set M →
    (∃ x, PSet.Mem x M ∧ PSet.Mem x set) →
      ∃ minimal, PSet.Mem minimal M ∧ PSet.Mem minimal set ∧
        ∀ y, PSet.Mem y M → PSet.Mem y minimal → ¬PSet.Mem y set

/-- Satisfaction of the Zermelo-Fraenkel axioms, including both schemas. -/
structure ModelsZF (M : PSet) : Prop where
  extensionality : ModelsExtensionality M
  emptySet : ModelsEmptySet M
  pairing : ModelsPairing M
  union : ModelsUnion M
  powerSet : ModelsPowerSet M
  infinity : ModelsInfinity M
  separation : ModelsSeparation M
  replacement : ModelsReplacement M
  foundation : ModelsFoundation M

/--
Choice in the disjoint-family form: every set of nonempty pairwise disjoint sets
has a set meeting each member in exactly one element.
-/
def ModelsChoice (M : PSet) : Prop :=
  ∀ family, PSet.Mem family M →
    (∀ member, PSet.Mem member M → PSet.Mem member family →
      ∃ x, PSet.Mem x M ∧ PSet.Mem x member) →
    (∀ left, PSet.Mem left M → PSet.Mem left family →
      ∀ right, PSet.Mem right M → PSet.Mem right family →
        ¬PSet.Equiv left right →
          ∀ x, PSet.Mem x M →
            ¬(PSet.Mem x left ∧ PSet.Mem x right)) →
    ∃ choice, PSet.Mem choice M ∧
      ∀ member, PSet.Mem member M → PSet.Mem member family →
        ∃ selected, PSet.Mem selected M ∧
          PSet.Mem selected member ∧ PSet.Mem selected choice ∧
          ∀ other, PSet.Mem other M → PSet.Mem other member →
            PSet.Mem other choice → PSet.Equiv other selected

/-- Satisfaction of ZFC is satisfaction of ZF together with Choice. -/
def ModelsZFC (M : PSet) : Prop :=
  ModelsZF M ∧ ModelsChoice M

/--
Every countable transitive model of ZF has a proper countable transitive ZF extension
with exactly the same ordinals. If the original model satisfies Choice, the extension
satisfies ZFC.
-/
theorem extensions_of_ctms
    (M : PSet)
    (hcountable : EquinumerousWithNat M)
    (htransitive : TransitiveSet M)
    (hZF : ModelsZF M) :
    ∃ N : PSet,
      ModelSubset M N ∧
        EquinumerousWithNat N ∧
        TransitiveSet N ∧
        ModelsZF N ∧
        ¬PSet.Equiv M N ∧
        (∀ ordinal, IsOrdinal ordinal →
          (PSet.Mem ordinal M ↔ PSet.Mem ordinal N)) ∧
        (ModelsChoice M → ModelsZFC N) := sorry

end ContinuumHypothesisUndecidability
