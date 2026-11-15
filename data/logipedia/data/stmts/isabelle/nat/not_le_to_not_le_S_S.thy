(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_le_to_not_le_S_S, catalog title "nat.not_le_to_not_le_S_S":
  if one natural number is not at most another, then their successors are
  likewise not ordered that way. This file contains no proof.
*)

theory not_le_to_not_le_S_S
  imports Main
begin

theorem not_le_to_not_le_S_S:
  "\<forall>n m :: nat. \<not> n \<le> m \<longrightarrow> \<not> Suc n \<le> Suc m"
  sorry

end
