(*
  Statement-only formalization of Logipedia corpus artifact nat.le_plus,
  catalog title "nat.le_plus": addition on natural numbers is monotone in
  both arguments. This file contains no proof.
*)

theory le_plus
  imports Main
begin

theorem le_plus:
  "\<forall>n1 n2 m1 m2 :: nat.
    n1 \<le> n2 \<longrightarrow>
    m1 \<le> m2 \<longrightarrow>
    n1 + m1 \<le> n2 + m2"
  sorry

end
