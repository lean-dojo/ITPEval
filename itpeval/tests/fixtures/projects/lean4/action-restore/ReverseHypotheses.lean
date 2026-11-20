/-- Reorder five hypotheses into a conjunction. -/
theorem reverse_hypotheses (P Q R S T : Prop) :
    P → Q → R → S → T → T ∧ S ∧ R ∧ Q ∧ P := by
  intro hp
  intro hq
  intro hr
  intro hs
  intro ht
  refine ⟨ht, ?_⟩
  refine ⟨hs, ?_⟩
  refine ⟨hr, ?_⟩
  refine ⟨hq, ?_⟩
  exact hp
