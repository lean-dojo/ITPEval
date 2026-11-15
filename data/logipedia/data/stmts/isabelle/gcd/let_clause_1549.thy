(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1549, catalog title "gcd.let_clause_1549": if a natural
  number n is positive and a natural number m is zero, then subtracting m
  from any natural number leaves it unchanged. This file contains no proof.
*)

theory let_clause_1549
  imports Main
begin

theorem let_clause_1549:
  "\<forall>m n :: nat.
    0 < n \<longrightarrow>
    0 = m \<longrightarrow>
    (\<forall>x1106 :: nat. x1106 = x1106 - m)"
  sorry

end
