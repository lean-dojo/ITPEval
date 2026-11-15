(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_le_to_lt_times, catalog title "nat.lt_to_le_to_lt_times": a strict
  product inequality on natural numbers from one strict comparison, one
  non-strict comparison, and positivity of the upper right factor. This file
  contains no proof.
*)

theory lt_to_le_to_lt_times
  imports Main
begin

theorem lt_to_le_to_lt_times:
  "\<forall>n m p q :: nat.
    n < m \<longrightarrow> p \<le> q \<longrightarrow> 0 < q \<longrightarrow>
    n * p < m * q"
  sorry

end
