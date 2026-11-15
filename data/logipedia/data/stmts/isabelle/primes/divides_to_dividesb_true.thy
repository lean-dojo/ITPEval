(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_dividesb_true, catalog title
  "primes.divides_to_dividesb_true": for positive natural divisors, divisibility
  implies that the Boolean zero-remainder test returns true. This file contains
  no proof.
*)

theory divides_to_dividesb_true
  imports Main
begin

definition dividesb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "dividesb n m \<longleftrightarrow> m mod n = 0"

theorem divides_to_dividesb_true:
  "\<forall>n m :: nat.
    0 < n \<longrightarrow> n dvd m \<longrightarrow> dividesb n m = True"
  sorry

end
