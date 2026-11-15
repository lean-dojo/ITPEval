(*
  Statement-only formalization of Logipedia corpus artifact nat.eq_minus_O,
  catalog title nat.eq_minus_O: subtracting a natural number from a lesser or
  equal natural number yields zero. This file contains no proof.
*)

theory eq_minus_O
  imports Main
begin

theorem eq_minus_O:
  "\<forall>n m :: nat. n \<le> m \<longrightarrow> n - m = 0"
  sorry

end
