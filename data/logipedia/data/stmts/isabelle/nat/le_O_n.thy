(*
  Statement-only formalization of Logipedia corpus artifact nat.le_O_n,
  catalog title "nat.le_O_n": zero is less than or equal to every natural
  number. This file contains no proof.
*)

theory le_O_n
  imports Main
begin

theorem logipedia_nat_le_O_n:
  "\<forall>n :: nat. 0 \<le> n"
  sorry

end
