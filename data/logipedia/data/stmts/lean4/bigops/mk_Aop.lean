-- Statement-only formalization of Logipedia corpus artifact "bigops.mk_Aop"
-- (catalog title "bigops.mk_Aop"): two-sided identity and associativity of a
-- binary operation imply the source predicate Aop at its neutral element.
-- This file contains no proof.

namespace bigops

-- itpeval-source-signature: logipedia:bigops.Aop as Aop
axiom Aop : (A : Type) → A → Prop

theorem mk_Aop :
    ∀ (A : Type) (nil : A) (op : A → A → A),
      (∀ a : A, op nil a = a) →
      (∀ a : A, op a nil = a) →
      (∀ a b c : A, op a (op b c) = op (op a b) c) →
      Aop A nil := sorry

end bigops
