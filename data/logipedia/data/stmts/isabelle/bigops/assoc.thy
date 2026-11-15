(*
  Statement-only formalization of Logipedia corpus artifact bigops.assoc:
  associativity of multiplication on natural numbers. This file contains no proof.
*)

theory assoc
  imports Main
begin

theorem bigops_assoc:
  "\<forall>a b c :: nat. a * (b * c) = (a * b) * c"
  sorry

end
