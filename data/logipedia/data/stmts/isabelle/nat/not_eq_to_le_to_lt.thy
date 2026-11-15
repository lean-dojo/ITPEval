(*
  Statement-only formalization of Logipedia corpus artifact
  nat.not_eq_to_le_to_lt, catalog title nat.not_eq_to_le_to_lt: distinct
  natural numbers in nondecreasing order are strictly ordered. This file
  contains no proof.
*)

theory not_eq_to_le_to_lt
  imports Main
begin

theorem not_eq_to_le_to_lt:
  "\<forall>n m :: nat.
    n \<noteq> m \<longrightarrow> n \<le> m \<longrightarrow> n < m"
  sorry

end
