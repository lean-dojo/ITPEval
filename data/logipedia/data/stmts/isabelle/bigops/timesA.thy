(*
  Statement-only formalization of Logipedia corpus artifact bigops.timesA:
  the abstract Aop predicate holds for one in the natural-number domain.
  This file contains no proof.
*)

theory timesA
  imports Main
begin

consts Aop :: "'a \<Rightarrow> bool"

theorem timesA:
  "Aop (Suc 0 :: nat)"
  sorry

end
