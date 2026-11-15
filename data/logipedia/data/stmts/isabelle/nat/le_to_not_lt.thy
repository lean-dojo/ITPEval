(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_not_lt, catalog title "nat.le_to_not_lt": a natural number less
  than or equal to another is not strictly greater than it. This file contains
  no proof.
*)

theory le_to_not_lt
  imports Main
begin

theorem le_to_not_lt:
  "\<forall>n m :: nat. n \<le> m \<longrightarrow> \<not> (m < n)"
  sorry

end
