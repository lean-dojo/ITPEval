(*
  Statement-only formalization of Logipedia corpus artifact nat.le_n_O_elim,
  catalog title "nat.le_n_O_elim": if a natural number is at most zero, then
  every predicate true at zero is true at that number. This file contains no
  proof.
*)

theory le_n_O_elim
  imports Main
begin

theorem le_n_O_elim:
  "\<forall>n :: nat. n \<le> 0 \<longrightarrow>
    (\<forall>P :: nat \<Rightarrow> bool. P 0 \<longrightarrow> P n)"
  sorry

end
