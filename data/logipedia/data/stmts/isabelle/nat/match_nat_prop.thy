(*
  Statement-only formalization of Logipedia corpus artifact
  nat.match_nat_prop, catalog title "nat.match_nat_prop": the natural-number
  case principle that a predicate holding at zero and at every successor holds
  for every natural number. This file contains no proof.
*)

theory match_nat_prop
  imports Main
begin

theorem match_nat_prop:
  "\<forall>P :: nat \<Rightarrow> bool.
    P 0 \<longrightarrow>
    (\<forall>n :: nat. P (Suc n)) \<longrightarrow>
    (\<forall>z :: nat. P z)"
  sorry

end
