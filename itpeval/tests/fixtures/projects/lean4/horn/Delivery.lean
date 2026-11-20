/-- Authorization and readiness for an item give a completion through delivery. -/
theorem completion_of_ready {α : Type} (item : α)
    (ready permitted delivered complete extra : α → Prop)
    (hready : ready item) (hpermitted : permitted item)
    (hdelivered : ready item → permitted item → delivered item)
    (hcomplete : delivered item → complete item) (_hextra : extra item) : complete item := by
  exact hcomplete (hdelivered hready hpermitted)
