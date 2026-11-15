(*
  Statement-only formalization of thousand-theorems corpus artifact Q632546
  (thousand-theorems__isabelle__Q632546), "Bertrand's postulate": every
  positive natural number has a prime strictly greater than it and at most
  twice it. This file contains no proof.
*)

theory Q632546_bertrand_s_postulate
  imports Main
begin

theorem bertrand_s_postulate:
  fixes n :: nat
  assumes "n \<noteq> 0"
  shows "\<exists>p::nat. prime p \<and> n < p \<and> p \<le> 2 * n"
  sorry

end
