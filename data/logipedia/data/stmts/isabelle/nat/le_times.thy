(*
  Statement-only formalization of Logipedia corpus artifact nat.le_times,
  catalog title "nat.le_times": multiplication is monotone in both arguments
  for natural numbers. This file contains no proof.
*)

theory le_times
  imports Main
begin

theorem le_times:
  "\<forall>n1 n2 m1 m2 :: nat.
    n1 \<le> n2 \<longrightarrow> m1 \<le> m2 \<longrightarrow>
    n1 * m1 \<le> n2 * m2"
  sorry

end
