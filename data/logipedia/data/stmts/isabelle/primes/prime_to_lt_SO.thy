(*
  Statement-only formalization of Logipedia corpus artifact
  primes.prime_to_lt_SO, catalog title "primes.prime_to_lt_SO": every natural
  number satisfying the source primality predicate is strictly greater than
  one. This file contains no proof.
*)

theory prime_to_lt_SO
  imports Main
begin

definition logipedia_divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_divides n m \<longleftrightarrow> (\<exists>q :: nat. m = n * q)"

definition logipedia_prime :: "nat \<Rightarrow> bool"
where
  "logipedia_prime n \<longleftrightarrow>
    1 < n \<and>
    (\<forall>m :: nat.
      logipedia_divides m n \<longrightarrow> 1 < m \<longrightarrow> m = n)"

theorem prime_to_lt_SO:
  "\<forall>p :: nat. logipedia_prime p \<longrightarrow> 1 < p"
  sorry

end
