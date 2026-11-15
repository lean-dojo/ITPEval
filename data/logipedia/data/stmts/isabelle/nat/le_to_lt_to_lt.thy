(*
  Statement-only formalization of Logipedia corpus artifact nat.le_to_lt_to_lt,
  catalog title "nat.le_to_lt_to_lt": mixed transitivity of less-than-or-equal
  and strict less-than on natural numbers. This file contains no proof.
*)

theory le_to_lt_to_lt
  imports Main
begin

theorem le_to_lt_to_lt:
  "\<forall>n m p :: nat. n \<le> m \<longrightarrow> m < p \<longrightarrow> n < p"
  sorry

end
