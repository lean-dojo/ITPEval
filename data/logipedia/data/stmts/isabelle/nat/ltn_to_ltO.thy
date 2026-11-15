(*
  Statement-only formalization of Logipedia corpus artifact nat.ltn_to_ltO,
  catalog title "nat.ltn_to_ltO": if one natural number is strictly less than
  another, then zero is strictly less than the latter. This file contains no
  proof.
*)

theory ltn_to_ltO
  imports Main
begin

theorem logipedia_nat_ltn_to_ltO:
  "\<forall>n m :: nat. n < m \<longrightarrow> 0 < m"
  sorry

end
