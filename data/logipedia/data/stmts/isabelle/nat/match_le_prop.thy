(*
  Statement-only formalization of Logipedia corpus artifact nat.match_le_prop,
  catalog title "nat.match_le_prop": a predicate holding at a natural-number
  lower bound and at every successor holds above that bound. This file contains
  no proof.
*)

theory match_le_prop
  imports Main
begin

theorem logipedia_nat_match_le_prop:
  "\<forall>(n :: nat) (P :: nat \<Rightarrow> bool).
    P n \<longrightarrow>
    (\<forall>m :: nat. P (Suc m)) \<longrightarrow>
    (\<forall>m :: nat. n \<le> m \<longrightarrow> P m)"
  sorry

end
