(*
  Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_n,
  catalog title "nat.not_le_Sn_n": no natural number's successor is less than
  or equal to that number. This file contains no proof.
*)

theory not_le_Sn_n
  imports Main
begin

theorem logipedia_nat_not_le_Sn_n:
  "\<forall>n :: nat. \<not> Suc n \<le> n"
  sorry

end
