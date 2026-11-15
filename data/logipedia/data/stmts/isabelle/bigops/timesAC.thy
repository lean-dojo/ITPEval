(*
  Statement-only formalization of Logipedia corpus artifact bigops.timesAC:
  the abstract ACop predicate holds for one in the natural-number domain.
  This file contains no proof.
*)

theory timesAC
  imports Main
begin

consts ACop :: "'a \<Rightarrow> bool"

theorem timesAC:
  "ACop (Suc 0 :: nat)"
  sorry

end
