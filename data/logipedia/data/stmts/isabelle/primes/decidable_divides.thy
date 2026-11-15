(*
  Statement-only formalization of Logipedia corpus artifact
  primes.decidable_divides, catalog title primes.decidable_divides:
  divisibility is decidable for every pair of natural numbers. This file
  contains no proof.
*)

theory decidable_divides
  imports Main
begin

definition logipedia_divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_divides n m \<longleftrightarrow> (\<exists>q :: nat. m = n * q)"

theorem decidable_divides:
  "\<forall>n m :: nat.
    logipedia_divides n m \<or> \<not> logipedia_divides n m"
  sorry

end
