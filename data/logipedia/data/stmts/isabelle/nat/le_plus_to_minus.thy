(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_minus, catalog title nat.le_plus_to_minus: a natural number
  bounded by p + m remains bounded by p after subtracting m. This file
  contains no proof.
*)

theory le_plus_to_minus
  imports Main
begin

theorem le_plus_to_minus:
  "\<forall>n m p :: nat. n \<le> p + m \<longrightarrow> n - m \<le> p"
  sorry

end
