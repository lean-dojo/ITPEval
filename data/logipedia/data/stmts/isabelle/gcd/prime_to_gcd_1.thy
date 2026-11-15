(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.prime_to_gcd_1, catalog title "gcd.prime_to_gcd_1": if a natural
  number n is prime and does not divide a natural number m, then their
  greatest common divisor is 1. This file contains no proof.
*)

theory prime_to_gcd_1
  imports Main
begin

definition logipedia_prime :: "nat \<Rightarrow> bool"
where
  "logipedia_prime n \<longleftrightarrow>
    1 < n \<and> (\<forall>d :: nat. d dvd n \<longrightarrow> 1 < d \<longrightarrow> d = n)"

theorem prime_to_gcd_1:
  "\<forall>n m :: nat.
    logipedia_prime n \<longrightarrow>
    \<not> n dvd m \<longrightarrow>
    gcd n m = 1"
  sorry

end
