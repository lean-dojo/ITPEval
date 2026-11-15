(*
  Statement-only formalization of "The Principle of Mathematical Induction" from Hundred
  Theorems item 074. It states that a predicate holding at zero and preserved by successor
  holds for every natural number. This file contains no proof.
*)

theory Principle_of_Mathematical_Induction
  imports Main
begin

theorem principle_of_mathematical_induction:
  "\<forall>P :: nat \<Rightarrow> bool.
    P 0 \<and> (\<forall>n. P n \<longrightarrow> P (Suc n))
    \<longrightarrow> (\<forall>n. P n)"
  sorry

end
