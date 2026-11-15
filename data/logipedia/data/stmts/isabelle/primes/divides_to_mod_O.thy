(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_mod_O, catalog title "primes.divides_to_mod_O": a positive
  natural number that divides another natural number leaves remainder zero.
  This file contains no proof.
*)

theory divides_to_mod_O
  imports Main
begin

definition logipedia_divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_divides n m \<longleftrightarrow> (\<exists>q :: nat. m = n * q)"

theorem divides_to_mod_O:
  fixes n m :: nat
  assumes "0 < n"
    and "logipedia_divides n m"
  shows "m mod n = 0"
  sorry

end
