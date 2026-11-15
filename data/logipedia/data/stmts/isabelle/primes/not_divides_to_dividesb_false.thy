(*
  Statement-only formalization of Logipedia corpus artifact
  primes.not_divides_to_dividesb_false, catalog title
  "primes.not_divides_to_dividesb_false": for positive natural divisors,
  non-divisibility implies that the Boolean zero-remainder test returns false.
  This file contains no proof.
*)

theory not_divides_to_dividesb_false
  imports Main
begin

definition dividesb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "dividesb n m \<longleftrightarrow> m mod n = 0"

theorem not_divides_to_dividesb_false:
  "\<forall>n m :: nat.
    0 < n \<longrightarrow> \<not> n dvd m \<longrightarrow> dividesb n m = False"
  sorry

end
