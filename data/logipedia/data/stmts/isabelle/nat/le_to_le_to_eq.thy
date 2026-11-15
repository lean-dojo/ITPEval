(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_le_to_eq, catalog title "nat.le_to_le_to_eq": antisymmetry of
  the natural-number order. This file contains no proof.
*)

theory le_to_le_to_eq
  imports Main
begin

theorem le_to_le_to_eq:
  "\<forall>n m :: nat. n \<le> m \<longrightarrow> m \<le> n \<longrightarrow> n = m"
  sorry

end
