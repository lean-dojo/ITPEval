(*
  Statement-only formalization of thousand-theorems corpus artifact Q1186808
  (thousand-theorems__isabelle__Q1186808), "Lucas's theorem": for a prime p,
  a binomial coefficient is congruent modulo p to the product of the binomial
  coefficients of the corresponding base-p digits, for any digit bound
  containing both indices. This file contains no proof.
*)

theory Q1186808_lucas_s_theorem
  imports Main
begin

theorem lucas_theorem:
  fixes n k p a :: nat
  assumes "prime p"
    and "n < p ^ a"
    and "k < p ^ a"
  shows
    "int (n choose k) mod int p =
      int (\<Prod>i<a. (n div p ^ i mod p) choose (k div p ^ i mod p))
        mod int p"
  sorry

end
