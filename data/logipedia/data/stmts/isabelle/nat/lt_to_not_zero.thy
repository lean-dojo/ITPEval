(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_not_zero, catalog title "nat.lt_to_not_zero": strict order between
  two natural numbers implies that the greater number is not zero. This file
  contains no proof.
*)

theory lt_to_not_zero
  imports Main
begin

theorem logipedia_nat_lt_to_not_zero:
  "\<forall>n m :: nat. n < m \<longrightarrow> m \<noteq> 0"
  sorry

end
