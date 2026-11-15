(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1551, catalog title gcd.let_clause_1551: for arbitrary
  natural numbers m and n, if n is zero then every natural multiplier leaves
  n unchanged under multiplication; m is intentionally unused. This file
  contains no proof.
*)

theory let_clause_1551
  imports Main
begin

theorem let_clause_1551:
  "\<forall>m n :: nat. 0 = n \<longrightarrow> (\<forall>x347 :: nat. n = x347 * n)"
  sorry

end
