/-- Readiness and permission yield completion through the delivery rule. -/
theorem completion_of_ready {α : Type} (item : α)
    (ready permitted delivered complete : α → Prop) :
    ready item → permitted item →
    (ready item → permitted item → delivered item) →
    (delivered item → complete item) → complete item := by
  intro hready hpermitted hdelivered hcomplete
  exact hcomplete (hdelivered hready hpermitted)
