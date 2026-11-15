(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a5
  (putnambench__isabelle__putnam_2025_a5): the sign sequences maximizing the
  number of permutations satisfying prescribed adjacent ascent or descent
  inequalities are exactly the two alternating sign sequences. This file
  contains no proof.
*)

theory putnam_2025_a5
  imports Main
begin

definition putnam_2025_a5_sign_sequence ::
    "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> bool" where
  "putnam_2025_a5_sign_sequence n s \<longleftrightarrow>
    (\<forall>i<n. s i = -1 \<or> s i = 1)"

definition putnam_2025_a5_permutation :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "putnam_2025_a5_permutation n p \<longleftrightarrow>
    length p = Suc n \<and>
    distinct p \<and>
    set p = {0..n}"

definition putnam_2025_a5_f ::
    "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat" where
  "putnam_2025_a5_f n s =
    card {p :: nat list.
      putnam_2025_a5_permutation n p \<and>
      (\<forall>i<n.
        0 < s i * (int (p ! Suc i) - int (p ! i)))}"

theorem putnam_2025_a5:
  fixes n :: nat
    and s :: "nat \<Rightarrow> int"
  assumes "1 \<le> n"
    and "putnam_2025_a5_sign_sequence n s"
  shows
    "(\<forall>t :: nat \<Rightarrow> int.
        putnam_2025_a5_sign_sequence n t \<longrightarrow>
          putnam_2025_a5_f n t \<le> putnam_2025_a5_f n s)
      \<longleftrightarrow>
      ((\<forall>i<n. s i = (-1 :: int) ^ (i + 1)) \<or>
       (\<forall>i<n. s i = (-1 :: int) ^ i))"
  sorry

end
