(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_S_S_to_not_le, catalog title "nat.not_le_S_S_to_not_le":
  failure of successor naturals to be ordered implies failure of their
  predecessors to be ordered. This file contains no proof.
*)

theory not_le_S_S_to_not_le
  imports Main
begin

theorem not_le_S_S_to_not_le:
  "\<forall>n m :: nat. \<not> Suc n \<le> Suc m \<longrightarrow> \<not> n \<le> m"
  sorry

end
