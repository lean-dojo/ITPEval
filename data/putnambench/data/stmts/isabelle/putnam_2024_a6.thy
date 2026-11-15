(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a6
  (putnambench__isabelle__putnam_2024_a6): the determinant of the Hankel
  matrix formed from the coefficients of the specified real power series is
  10 raised to n(n-1)/2. This file contains no proof.
*)

theory putnam_2024_a6
  imports Complex_Main
begin

definition putnam_2024_a6_det ::
    "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "putnam_2024_a6_det A n =
    (\<Sum>p\<in>{p :: nat \<Rightarrow> nat.
        bij_betw p {0..<n} {0..<n} \<and>
        (\<forall>i \<ge> n. p i = i)}.
      (-1 :: real) ^
        card {(i, j). i < n \<and> j < n \<and> i < j \<and> p j < p i} *
      (\<Prod>i\<in>{0..<n}. A i (p i)))"

definition putnam_2024_a6_solution :: "nat \<Rightarrow> real" where
  "putnam_2024_a6_solution n =
    10 ^ (n * (n - 1) div 2)"

theorem putnam_2024_a6:
  fixes c :: "nat \<Rightarrow> real"
    and n :: nat
  assumes hseries:
    "eventually
      (\<lambda>x :: real.
        (\<lambda>k :: nat. c k * x ^ k) sums
          ((1 - 3 * x - sqrt (1 - 14 * x + 9 * x ^ 2)) / 4))
      (nhds 0)"
    and hn: "0 < n"
  shows
    "putnam_2024_a6_det (\<lambda>i j. c (i + j + 1)) n =
      putnam_2024_a6_solution n"
  sorry

end
