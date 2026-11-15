(*
  Statement-only formalization of Logipedia corpus artifact
  nat.plus_minus_m_m, catalog title nat.plus_minus_m_m: for natural numbers
  m and n with m at most n, adding m back after subtracting it from n
  recovers n. This file contains no proof.
*)

theory plus_minus_m_m
  imports Main
begin

theorem plus_minus_m_m:
  "\<forall>n m :: nat. m \<le> n \<longrightarrow> n = (n - m) + m"
  sorry

end
