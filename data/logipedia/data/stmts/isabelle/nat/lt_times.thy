(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_times,
  catalog title "nat.lt_times": strict inequalities between natural numbers
  are preserved when the corresponding factors are multiplied. This file
  contains no proof.
*)

theory lt_times
  imports Main
begin

theorem lt_times:
  "\<forall>n m p q :: nat.
    n < m \<longrightarrow> p < q \<longrightarrow> n * p < m * q"
  sorry

end
