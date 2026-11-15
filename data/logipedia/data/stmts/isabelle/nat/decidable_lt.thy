(*
  Statement-only formalization of Logipedia corpus artifact nat.decidable_lt,
  catalog title "nat.decidable_lt": strict less-than is decidable for every
  pair of natural numbers. This file contains no proof.
*)

theory decidable_lt
  imports Main
begin

theorem decidable_lt:
  "\<forall>n m :: nat. n < m \<or> \<not> (n < m)"
  sorry

end
