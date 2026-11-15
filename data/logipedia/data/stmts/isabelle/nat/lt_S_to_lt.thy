(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_S_to_lt,
  catalog title "nat.lt_S_to_lt": strict-order descent from a successor to
  its predecessor on natural numbers. This file contains no proof.
*)

theory lt_S_to_lt
  imports Main
begin

theorem lt_S_to_lt:
  "\<forall>n m :: nat. Suc n < m \<longrightarrow> n < m"
  sorry

end
