universe u

namespace GraphPath

variable {V : Type u}

def Edge (V : Type u) := V → V → Prop

inductive Path (E : Edge V) : V → V → Prop
| nil  : ∀ v, Path E v v
| step : ∀ {u v w}, Path E u v → E v w → Path E u w


variable {E : Edge V}

theorem refl (v : V) : Path (E:=E) v v := Path.nil v

theorem trans {u v w : V} : Path (E:=E) u v → Path (E:=E) v w → Path (E:=E) u w := by sorry
def Erev (E : Edge V) : Edge V := fun x y => E y x

def undirected (E : Edge V) : Prop := ∀ x y, E x y → E y x

theorem reverse_path {u v : V} (hE : undirected E) :
  Path (E:=E) u v → Path (E:=E) v u := by sorry
theorem concat_edge_right {u v w : V} :
  Path (E:=E) u v → E v w → Path (E:=E) u w := by sorry
theorem concat {u v w : V} :
  Path (E:=E) u v → Path (E:=E) v w → Path (E:=E) u w := by sorry
theorem edge_path {u v : V} : E u v → Path (E:=E) u v := by sorry
theorem concat_edge_left {u v w : V} :
  E u v → Path (E:=E) v w → Path (E:=E) u w := by sorry
theorem concat3 {u v w t : V} :
  Path (E:=E) u v → Path (E:=E) v w → Path (E:=E) w t → Path (E:=E) u t := by sorry
theorem reverse_in_Erev {u v : V} :
  Path (E:=E) u v → Path (E:=Erev E) v u := by sorry
theorem cycle_refl {v w : V} :
  Path (E:=E) v w → Path (E:=E) w v → Path (E:=E) v v := by sorry
end GraphPath
