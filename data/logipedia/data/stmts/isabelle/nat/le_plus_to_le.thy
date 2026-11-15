(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_to_le,
  catalog title "nat.le_plus_to_le": cancellation of a common left addend from
  an inequality between natural numbers. This file contains no proof.
*)

theory le_plus_to_le
  imports Main
begin

theorem logipedia_nat_le_plus_to_le:
  "\<forall>a n m :: nat. a + n \<le> a + m \<longrightarrow> n \<le> m"
  sorry

end
