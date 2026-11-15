(*
  Statement-only formalization of PutnamBench artifact putnam_2023_b3,
  concerning the expected length of the longest zigzag subsequence of
  independent uniform random variables on the unit interval. This file
  contains no proof.
*)

theory putnam_2023_b3
  imports Complex_Main
begin

definition putnam_2023_b3_sigma_algebra ::
    "'a set set \<Rightarrow> bool" where
  "putnam_2023_b3_sigma_algebra E \<longleftrightarrow>
    UNIV \<in> E \<and>
    (\<forall>A\<in>E. UNIV - A \<in> E) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>m. A m \<in> E) \<longrightarrow> (\<Union>m. A m) \<in> E)"

definition putnam_2023_b3_borel_sets :: "real set set" where
  "putnam_2023_b3_borel_sets =
    \<Inter>{E :: real set set.
      putnam_2023_b3_sigma_algebra E \<and> {U. open U} \<subseteq> E}"

definition putnam_2023_b3_probability_measure ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> bool" where
  "putnam_2023_b3_probability_measure E P \<longleftrightarrow>
    putnam_2023_b3_sigma_algebra E \<and>
    P {} = 0 \<and>
    P UNIV = 1 \<and>
    (\<forall>A\<in>E. 0 \<le> P A) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>m. A m \<in> E) \<longrightarrow>
      (\<forall>m l. m \<noteq> l \<longrightarrow> A m \<inter> A l = {}) \<longrightarrow>
      P (\<Union>m. A m) = (\<Sum>m. P (A m)))"

definition putnam_2023_b3_real_random_variable ::
    "'a set set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "putnam_2023_b3_real_random_variable E f \<longleftrightarrow>
    (\<forall>B\<in>putnam_2023_b3_borel_sets. f -` B \<in> E)"

definition putnam_2023_b3_uniform_on_unit_interval ::
    "('a set \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "putnam_2023_b3_uniform_on_unit_interval P f \<longleftrightarrow>
    (\<forall>t. P {\<omega>. f \<omega> \<le> t} =
      (if t < 0 then 0 else if t \<le> 1 then t else 1))"

definition putnam_2023_b3_independent ::
    "('a set \<Rightarrow> real) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "putnam_2023_b3_independent P X n \<longleftrightarrow>
    (\<forall>J A.
      finite J \<longrightarrow>
      J \<subseteq> {..<n} \<longrightarrow>
      (\<forall>j\<in>J. A j \<in> putnam_2023_b3_borel_sets) \<longrightarrow>
      P (\<Inter>j\<in>J. X j -` A j) =
        (\<Prod>j\<in>J. P (X j -` A j)))"

definition putnam_2023_b3_is_zigzag ::
    "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool" where
  "putnam_2023_b3_is_zigzag k y \<longleftrightarrow>
    k = 1 \<or>
    ((\<forall>i. i + 1 < k \<longrightarrow> y (i + 1) \<noteq> y i) \<and>
      (\<forall>i. i + 2 < k \<longrightarrow>
        (y (i + 2) < y (i + 1) \<longleftrightarrow> y i < y (i + 1))))"

definition putnam_2023_b3_is_zigzag_subsequence ::
    "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "putnam_2023_b3_is_zigzag_subsequence n x k \<longleftrightarrow>
    (\<exists>indices :: nat \<Rightarrow> nat.
      (\<forall>j<k. indices j < n) \<and>
      (\<forall>j<k. \<forall>l<k. j < l \<longrightarrow> indices j < indices l) \<and>
      putnam_2023_b3_is_zigzag k (\<lambda>j. x (indices j)))"

theorem putnam_2023_b3:
  fixes E :: "'a set set"
    and P :: "'a set \<Rightarrow> real"
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and a :: "'a \<Rightarrow> nat"
    and n :: nat
  assumes hn: "2 \<le> n"
    and probability_space: "putnam_2023_b3_probability_measure E P"
    and X_measurable:
      "\<And>i. i < n \<Longrightarrow>
        putnam_2023_b3_real_random_variable E (X i)"
    and X_uniform:
      "\<And>i. i < n \<Longrightarrow>
        putnam_2023_b3_uniform_on_unit_interval P (X i)"
    and X_independent: "putnam_2023_b3_independent P X n"
    and a_def:
      "\<And>\<omega>. a \<omega> =
        Max {k. putnam_2023_b3_is_zigzag_subsequence n
          (\<lambda>i. X i \<omega>) k}"
  shows "(\<Sum>k\<le>n. real k * P {\<omega>. a \<omega> = k}) =
    (2 * real n + 2) / 3"
  sorry

end
