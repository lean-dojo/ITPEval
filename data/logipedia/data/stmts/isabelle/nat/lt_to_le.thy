(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_to_le,
  catalog title "nat.lt_to_le": strict inequality between natural numbers
  implies non-strict inequality. This file contains no proof.
*)

theory lt_to_le
  imports Main
begin

theorem logipedia_nat_lt_to_le:
  "\<forall>x y :: nat. x < y \<longrightarrow> x \<le> y"
  sorry

end
