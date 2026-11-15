(*
  Statement-only formalization of Logipedia corpus artifact nat.not_lt_to_le,
  catalog title "nat.not_lt_to_le": on natural numbers, not being strictly less
  implies the reverse less-than-or-equal relation. This file contains no proof.
*)

theory not_lt_to_le
  imports Main
begin

theorem logipedia_nat_not_lt_to_le:
  "\<forall>n m :: nat. \<not> (n < m) \<longrightarrow> m \<le> n"
  sorry

end
