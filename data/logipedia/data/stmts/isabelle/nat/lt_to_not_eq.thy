(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_to_not_eq,
  catalog title "nat.lt_to_not_eq": strict order between two natural numbers
  implies that the numbers are unequal. This file contains no proof.
*)

theory lt_to_not_eq
  imports Main
begin

theorem logipedia_nat_lt_to_not_eq:
  "\<forall>n m :: nat. n < m \<longrightarrow> n \<noteq> m"
  sorry

end
