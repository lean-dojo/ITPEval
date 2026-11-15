(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_to_le_to_lt,
  catalog title "nat.lt_to_le_to_lt": mixed transitivity of strict less-than
  and less-than-or-equal on natural numbers. This file contains no proof.
*)

theory lt_to_le_to_lt
  imports Main
begin

theorem lt_to_le_to_lt:
  "\<forall>n m p :: nat. n < m \<longrightarrow> m \<le> p \<longrightarrow> n < p"
  sorry

end
