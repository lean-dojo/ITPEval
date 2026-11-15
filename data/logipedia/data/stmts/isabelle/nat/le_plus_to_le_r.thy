(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_le_r, catalog title "nat.le_plus_to_le_r": cancellation of
  a common right addend from an inequality of natural numbers. This file
  contains no proof.
*)

theory le_plus_to_le_r
  imports Main
begin

theorem le_plus_to_le_r:
  "\<forall>a n m :: nat. n + a \<le> m + a \<longrightarrow> n \<le> m"
  sorry

end
