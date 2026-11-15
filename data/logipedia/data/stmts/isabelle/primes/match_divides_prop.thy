(*
  Statement-only formalization of Logipedia corpus artifact
  primes.match_divides_prop, catalog title "primes.match_divides_prop":
  elimination of natural-number divisibility into an arbitrary proposition
  from a continuation for every factor witness. This file contains no proof.
*)

theory match_divides_prop
  imports Main
begin

theorem match_divides_prop:
  "\<forall>n m :: nat. \<forall>return :: bool.
    (\<forall>q :: nat. m = n * q \<longrightarrow> return) \<longrightarrow>
    n dvd m \<longrightarrow> return"
  sorry

end
