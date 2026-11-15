(*
  Statement-only formalization of Logipedia corpus artifact
  primes.let_clause_15311, catalog title "primes.let_clause_15311": for
  natural numbers n and m, positivity and divisibility assumptions together
  with m = n * Suc p imply m = n + n * p; the source's unused universal
  natural d is retained. This file contains no proof.
*)

theory let_clause_15311
  imports Main
begin

theorem let_clause_15311:
  "\<forall>n m :: nat.
    0 < m \<longrightarrow>
    n dvd m \<longrightarrow>
    (\<forall>d p :: nat.
      m = n * Suc p \<longrightarrow>
      m = n + n * p)"
  sorry

end
