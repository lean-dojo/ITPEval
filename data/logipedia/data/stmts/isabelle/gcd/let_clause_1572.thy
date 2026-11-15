(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1572, catalog title "gcd.let_clause_1572": for natural
  numbers m and n, if n is positive, their greatest common divisor is zero,
  and both m and n are zero, then m is zero. This file contains no proof.
*)

theory let_clause_1572
  imports Main
begin

theorem let_clause_1572:
  "\<forall>m n :: nat.
    0 < n \<longrightarrow>
    gcd m n = 0 \<longrightarrow>
    m = 0 \<longrightarrow>
    n = 0 \<longrightarrow>
    m = 0"
  sorry

end
