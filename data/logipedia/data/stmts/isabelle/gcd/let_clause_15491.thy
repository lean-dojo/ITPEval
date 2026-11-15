(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_15491, catalog title "gcd.let_clause_15491": if a natural
  number n is zero, then subtracting n from any natural number leaves it
  unchanged; an additional natural number m is universally quantified.
  This file contains no proof.
*)

theory let_clause_15491
  imports Main
begin

theorem let_clause_15491:
  "\<forall>m n :: nat.
    0 = n \<longrightarrow>
    (\<forall>x1106 :: nat. x1106 = x1106 - n)"
  sorry

end
