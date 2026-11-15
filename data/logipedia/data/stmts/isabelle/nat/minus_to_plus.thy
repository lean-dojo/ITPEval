(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_to_plus,
  catalog title "nat.minus_to_plus": if m is at most n and the truncated
  natural-number difference n - m equals p, then n equals m + p. This file
  contains no proof.
*)

theory minus_to_plus
  imports Main
begin

theorem minus_to_plus:
  "\<forall>n m p :: nat.
    m \<le> n \<longrightarrow> n - m = p \<longrightarrow> n = m + p"
  sorry

end
