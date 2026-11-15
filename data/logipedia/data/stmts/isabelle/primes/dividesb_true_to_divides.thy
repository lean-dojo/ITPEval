(*
  Statement-only formalization of Logipedia corpus artifact
  primes.dividesb_true_to_divides, catalog title
  "primes.dividesb_true_to_divides": a true Boolean zero-remainder test entails
  divisibility for natural numbers. This file contains no proof.
*)

theory dividesb_true_to_divides
  imports Main
begin

definition logipedia_divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_divides n m \<longleftrightarrow> (\<exists>q :: nat. m = n * q)"

definition dividesb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "dividesb n m \<longleftrightarrow> m mod n = 0"

theorem dividesb_true_to_divides:
  "\<forall>n m :: nat.
    dividesb n m = True \<longrightarrow> logipedia_divides n m"
  sorry

end
