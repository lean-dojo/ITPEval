(*
  Statement-only formalization of thousand-theorems corpus artifact Q1457052,
  (thousand-theorems__isabelle__Q1457052), "Well-ordering theorem": every
  arbitrary type admits a binary relation that well-orders its entire carrier.
  This file contains no proof.
*)

theory Q1457052_well_ordering_theorem
  imports Main
begin

theorem exists_well_order:
  "\<exists>r :: ('a \<times> 'a) set. well_order_on UNIV r"
  sorry

end
