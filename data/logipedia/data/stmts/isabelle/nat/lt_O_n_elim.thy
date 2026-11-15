(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_O_n_elim,
  catalog title "nat.lt_O_n_elim": a positive natural number satisfies every
  predicate that holds of all successors. This file contains no proof.
*)

theory lt_O_n_elim
  imports Main
begin

theorem logipedia_nat_lt_O_n_elim:
  "\<forall>(n :: nat) (P :: nat \<Rightarrow> bool).
    0 < n \<longrightarrow>
    (\<forall>m :: nat. P (Suc m)) \<longrightarrow>
    P n"
  sorry

end
