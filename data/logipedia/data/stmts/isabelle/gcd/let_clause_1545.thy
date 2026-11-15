(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1545, catalog title "gcd.let_clause_1545": a nested
  natural-number implication from a zero greatest common divisor and
  zero-divisibility assumptions, through universally quantified quotient
  equalities, to the conclusion that the first input is zero. This file
  contains no proof.
*)

theory let_clause_1545
  imports Main
begin

theorem let_clause_1545:
  "\<forall>m n :: nat.
    gcd m n = 0 \<longrightarrow>
    0 dvd n \<longrightarrow>
    (\<forall>q1 :: nat.
      n = 0 * q1 \<longrightarrow>
      0 dvd m \<longrightarrow>
      (\<forall>q2 :: nat.
        m = 0 * q2 \<longrightarrow>
        m = 0))"
  sorry

end
