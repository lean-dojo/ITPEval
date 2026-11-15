(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_S_S_to_le, catalog title "nat.le_S_S_to_le": successor cancellation
  for the natural-number order. This file contains no proof.
*)

theory le_S_S_to_le
  imports Main
begin

theorem le_S_S_to_le:
  "\<forall>n m :: nat. Suc n \<le> Suc m \<longrightarrow> n \<le> m"
  sorry

end
