(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus_b,
  catalog title "nat.le_plus_b": if the sum of two natural numbers n and b is
  at most m, then n is at most m. This file contains no proof.
*)

theory le_plus_b
  imports Main
begin

theorem le_plus_b:
  "\<forall>b n m :: nat. n + b \<le> m \<longrightarrow> n \<le> m"
  sorry

end
