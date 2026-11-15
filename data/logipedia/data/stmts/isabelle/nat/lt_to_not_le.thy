(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_not_le, catalog title nat.lt_to_not_le: strict inequality of
  natural numbers implies that the reverse non-strict inequality does not
  hold. This file contains no proof.
*)

theory lt_to_not_le
  imports Main
begin

theorem lt_to_not_le:
  "\<forall>n m :: nat. n < m \<longrightarrow> \<not> (m \<le> n)"
  sorry

end
