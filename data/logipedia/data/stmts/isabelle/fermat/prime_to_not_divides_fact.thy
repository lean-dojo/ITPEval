(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.prime_to_not_divides_fact, catalog title
  fermat.prime_to_not_divides_fact: a prime natural number does not divide
  the factorial of any smaller natural number. This file contains no proof.
*)

theory prime_to_not_divides_fact
  imports Main
begin

theorem prime_to_not_divides_fact:
  "\<forall>p :: nat. prime p \<longrightarrow>
    (\<forall>n :: nat. n < p \<longrightarrow> \<not> p dvd fact n)"
  sorry

end
