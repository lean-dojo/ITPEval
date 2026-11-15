(*
  Statement-only formalization of Logipedia corpus artifact
  primes.dividesb_false_to_not_divides, catalog title
  "primes.dividesb_false_to_not_divides": a false Boolean zero-remainder test
  entails non-divisibility for natural numbers. This file contains no proof.
*)

theory dividesb_false_to_not_divides
  imports Main
begin

definition logipedia_divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_divides n m \<longleftrightarrow> (\<exists>q :: nat. m = n * q)"

definition dividesb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "dividesb n m \<longleftrightarrow> m mod n = 0"

theorem dividesb_false_to_not_divides:
  "\<forall>n m :: nat.
    dividesb n m = False \<longrightarrow> \<not> logipedia_divides n m"
  sorry

end
