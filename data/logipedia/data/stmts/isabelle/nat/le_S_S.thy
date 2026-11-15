(*
  Statement-only formalization of Logipedia corpus artifact nat.le_S_S,
  catalog title nat.le_S_S: successor preserves the less-than-or-equal
  relation on natural numbers. This file contains no proof.
*)

theory le_S_S
  imports Main
begin

theorem logipedia_nat_le_S_S:
  "\<forall>n m :: nat. n \<le> m \<longrightarrow> Suc n \<le> Suc m"
  sorry

end
