(*
  Statement-only formalization of Logipedia corpus artifact
  primes.mod_O_to_divides, catalog title "primes.mod_O_to_divides": for a
  positive natural number, zero remainder implies that it divides the
  dividend. This file contains no proof.
*)

theory mod_O_to_divides
  imports Main
begin

definition logipedia_divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_divides n m \<longleftrightarrow> (\<exists>q :: nat. m = n * q)"

theorem mod_O_to_divides:
  fixes n m :: nat
  assumes "0 < n"
    and "m mod n = 0"
  shows "logipedia_divides n m"
  sorry

end
