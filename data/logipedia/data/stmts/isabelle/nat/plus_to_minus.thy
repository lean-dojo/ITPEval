(*
  Statement-only formalization of Logipedia corpus artifact
  nat.plus_to_minus, catalog title "nat.plus_to_minus": if a natural number
  is the sum of m and p, subtracting m yields p. This file contains no proof.
*)

theory plus_to_minus
  imports Main
begin

theorem plus_to_minus:
  "\<forall>n m p :: nat. n = m + p \<longrightarrow> n - m = p"
  sorry

end
