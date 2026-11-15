(*
  Statement-only formalization of Logipedia corpus artifact nat.le_ind,
  catalog title "nat.le_ind": induction for a predicate on natural numbers
  above an arbitrary lower bound. This file contains no proof.
*)

theory le_ind
  imports Main
begin

theorem logipedia_nat_le_ind:
  "\<forall>(n :: nat) (Q :: nat \<Rightarrow> bool).
    Q n \<longrightarrow>
    (\<forall>m :: nat. n \<le> m \<longrightarrow> Q m \<longrightarrow> Q (Suc m)) \<longrightarrow>
    (\<forall>m :: nat. n \<le> m \<longrightarrow> Q m)"
  sorry

end
