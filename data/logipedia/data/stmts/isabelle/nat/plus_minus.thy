(*
  Statement-only formalization of Logipedia corpus artifact nat.plus_minus,
  catalog title nat.plus_minus: adding after truncated natural subtraction
  agrees with subtracting from the enlarged minuend when m is at most n.
  This file contains no proof.
*)

theory plus_minus
  imports Main
begin

theorem plus_minus:
  "\<forall>m n p :: nat. m \<le> n \<longrightarrow> (n - m) + p = (n + p) - m"
  sorry

end
