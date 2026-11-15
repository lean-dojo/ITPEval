(*
  Statement-only formalization of Logipedia corpus artifact
  primes.let_clause_1531, catalog title "primes.let_clause_1531": for natural
  numbers n and m, positivity and divisibility assumptions together with
  m = n * 0 imply m = 0; the source's unused universal natural d is retained.
  This file contains no proof.
*)

theory let_clause_1531
  imports Main
begin

theorem let_clause_1531:
  "\<forall>n m :: nat.
    0 < m \<longrightarrow>
    n dvd m \<longrightarrow>
    (\<forall>d :: nat. m = n * 0 \<longrightarrow> m = 0)"
  sorry

end
