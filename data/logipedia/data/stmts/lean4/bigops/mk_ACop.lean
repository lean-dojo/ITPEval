-- Statement-only formalization of Logipedia corpus artifact "bigops.mk_ACop"
-- (catalog title "bigops.mk_ACop"): two-sided identity, associativity, and
-- commutativity of a binary operation imply the source predicate ACop at its
-- neutral element. This file contains no proof.

namespace bigops

-- itpeval-source-signature: logipedia:bigops.ACop as ACop
axiom ACop : (A : Type) → A → Prop

theorem mk_ACop :
    ∀ (A : Type) (nil : A) (op : A → A → A),
      (∀ a : A, op nil a = a) →
      (∀ a : A, op a nil = a) →
      (∀ a b c : A, op a (op b c) = op (op a b) c) →
      (∀ a b : A, op a b = op b a) →
      ACop A nil := sorry

end bigops
