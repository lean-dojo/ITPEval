(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_b4
  (putnambench__isabelle__putnam_2025_b4): an upper bound for the sum of the
  entries of a nonnegative-integer matrix with a zero triangular region and
  unit-step changes along rows and columns. This file contains no proof.
*)

theory putnam_2025_b4
  imports Main
begin

theorem putnam_2025_b4:
  fixes m S N :: nat
    and A :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  assumes ha:
    "\<forall>i<m + 2. \<forall>j<m + 2.
      i + j \<le> m \<longrightarrow> A i j = 0"
    and hb:
    "\<forall>i<m + 1. \<forall>j<m + 2.
      A (i + 1) j = A i j \<or> A (i + 1) j = A i j + 1"
    and hc:
    "\<forall>i<m + 2. \<forall>j<m + 1.
      A i (j + 1) = A i j \<or> A i (j + 1) = A i j + 1"
    and hS: "S = (\<Sum>i<m + 2. \<Sum>j<m + 2. A i j)"
    and hN:
      "N = card {(i, j). i < m + 2 \<and> j < m + 2 \<and> A i j \<noteq> 0}"
  shows "3 * S \<le> (m + 4) * N"
  sorry

end
