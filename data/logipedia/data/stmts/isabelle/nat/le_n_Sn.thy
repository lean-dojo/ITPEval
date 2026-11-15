(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n_Sn,
  catalog title nat.le_n_Sn: every natural number is less than or equal to
  its successor. This file contains no proof.
*)

theory le_n_Sn
  imports Main
begin

theorem le_n_Sn:
  "\<forall>n :: nat. n \<le> Suc n"
  sorry

end
