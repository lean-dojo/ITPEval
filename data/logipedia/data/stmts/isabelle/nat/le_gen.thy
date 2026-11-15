(*
  Statement-only formalization of Logipedia corpus artifact nat.le_gen,
  catalog title nat.le_gen: any predicate holding for every natural number at
  most a given natural number holds for that number itself. This file contains
  no proof.
*)

theory le_gen
  imports Main
begin

theorem le_gen:
  "\<forall>(P :: nat \<Rightarrow> bool) (n :: nat).
    (\<forall>i :: nat. i \<le> n \<longrightarrow> P i) \<longrightarrow> P n"
  sorry

end
