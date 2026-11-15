(*
  Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_O,
  catalog title "nat.not_le_Sn_O": the successor of every natural number is
  not less than or equal to zero. This file contains no proof.
*)

theory not_le_Sn_O
  imports Main
begin

theorem logipedia_nat_not_le_Sn_O:
  "\<forall>n :: nat. \<not> Suc n \<le> 0"
  sorry

end
