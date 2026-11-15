(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n_O_to_eq,
  catalog title "nat.le_n_O_to_eq": a natural number at most zero is equal to
  zero. This file contains no proof.
*)

theory le_n_O_to_eq
  imports Main
begin

theorem le_n_O_to_eq:
  "\<forall>n :: nat. n \<le> 0 \<longrightarrow> 0 = n"
  sorry

end
