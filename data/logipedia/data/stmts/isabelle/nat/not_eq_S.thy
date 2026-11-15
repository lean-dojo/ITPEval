(*
  Statement-only formalization of Logipedia corpus artifact nat.not_eq_S,
  catalog title "nat.not_eq_S": distinct natural numbers remain distinct
  after applying the successor operation. This file contains no proof.
*)

theory not_eq_S
  imports Main
begin

theorem not_eq_S:
  "\<forall>n m :: nat. n \<noteq> m \<longrightarrow> Suc n \<noteq> Suc m"
  sorry

end
