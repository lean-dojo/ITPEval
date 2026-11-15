(*
  Statement-only formalization of Logipedia corpus artifact nat.decidable_le,
  catalog title nat.decidable_le: the natural-number less-than-or-equal
  relation is decidable for every pair of natural numbers. This file contains
  no proof.
*)

theory decidable_le
  imports Main
begin

theorem decidable_le:
  "\<forall>n m :: nat. (n \<le> m) \<or> \<not> (n \<le> m)"
  sorry

end
