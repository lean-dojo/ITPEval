(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_to_or_lt_eq, catalog title "nat.le_to_or_lt_eq": for natural numbers,
  a less-than-or-equal relation implies strict inequality or equality. This
  file contains no proof.
*)

theory le_to_or_lt_eq
  imports Main
begin

theorem le_to_or_lt_eq:
  "\<forall>n m :: nat. n \<le> m \<longrightarrow> n < m \<or> n = m"
  sorry

end
