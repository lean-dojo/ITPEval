(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a4
  (putnambench__isabelle__putnam_2025_a4): the least dimension of real square
  matrices whose commuting pairs among 2025 indexed matrices are exactly the
  equal or cyclically adjacent indices. This file contains no proof.
*)

theory putnam_2025_a4
  imports Complex_Main
begin

type_synonym putnam_2025_a4_matrix = "nat \<Rightarrow> nat \<Rightarrow> real"

definition putnam_2025_a4_matrix_mult ::
    "nat \<Rightarrow> putnam_2025_a4_matrix \<Rightarrow> putnam_2025_a4_matrix \<Rightarrow>
      putnam_2025_a4_matrix" where
  "putnam_2025_a4_matrix_mult k A B =
    (\<lambda>i j. \<Sum>r<k. A i r * B r j)"

definition putnam_2025_a4_commute ::
    "nat \<Rightarrow> putnam_2025_a4_matrix \<Rightarrow> putnam_2025_a4_matrix \<Rightarrow>
      bool" where
  "putnam_2025_a4_commute k A B \<longleftrightarrow>
    (\<forall>i<k. \<forall>j<k.
      putnam_2025_a4_matrix_mult k A B i j =
        putnam_2025_a4_matrix_mult k B A i j)"

definition putnam_2025_a4_admissible_dimension :: "nat \<Rightarrow> bool" where
  "putnam_2025_a4_admissible_dimension k \<longleftrightarrow>
    (\<exists>A :: nat \<Rightarrow> putnam_2025_a4_matrix.
      \<forall>i<2025. \<forall>j<2025.
        i \<le> j \<longrightarrow>
          (putnam_2025_a4_commute k (A i) (A j) \<longleftrightarrow>
            j - i \<in> {0, 1, 2024}))"

definition putnam_2025_a4_solution :: nat where
  "putnam_2025_a4_solution = 3"

theorem putnam_2025_a4:
  shows
    "putnam_2025_a4_solution
        \<in> {k. putnam_2025_a4_admissible_dimension k} \<and>
      (\<forall>k\<in>{k. putnam_2025_a4_admissible_dimension k}.
        putnam_2025_a4_solution \<le> k)"
  sorry

end
