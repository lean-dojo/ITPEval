(*
  Statement-only formalization of Logipedia corpus artifact nat.minus_minus,
  catalog title nat.minus_minus: for natural numbers n, m, and p with p at
  most m and m at most n, p plus the difference n minus m equals n minus the
  difference m minus p, using truncated natural-number subtraction. This file
  contains no proof.
*)

theory minus_minus
  imports Main
begin

theorem logipedia_nat_minus_minus:
  "\<forall>n m p :: nat.
    p \<le> m \<longrightarrow> m \<le> n \<longrightarrow>
    p + (n - m) = n - (m - p)"
  sorry

end
