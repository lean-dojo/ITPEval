(*
  Statement-only formalization of Logipedia corpus artifact nat.not_le_to_lt,
  catalog title "nat.not_le_to_lt": for natural numbers, failure of one to be
  less than or equal to another implies the reverse strict inequality. This
  file contains no proof.
*)

theory not_le_to_lt
  imports Main
begin

theorem logipedia_nat_not_le_to_lt:
  "\<forall>n m :: nat. \<not> (n \<le> m) \<longrightarrow> m < n"
  sorry

end
