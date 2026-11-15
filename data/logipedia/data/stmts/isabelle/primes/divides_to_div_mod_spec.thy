(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_div_mod_spec, catalog title
  "primes.divides_to_div_mod_spec": a positive natural divisor of a natural
  number yields its Euclidean division specification with remainder zero.
  This file contains no proof.
*)

theory divides_to_div_mod_spec
  imports Main
begin

definition logipedia_divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_divides n m \<longleftrightarrow> (\<exists>q. m = n * q)"

definition div_mod_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "div_mod_spec a b q r \<longleftrightarrow> r < b \<and> a = q * b + r"

theorem divides_to_div_mod_spec:
  fixes n m :: nat
  assumes "0 < n"
    and "logipedia_divides n m"
  shows "div_mod_spec m n (m div n) 0"
  sorry

end
