(*
  Statement-only formalization of PutnamBench artifact putnam_2024_b4,
  concerning a random nearest-step recurrence driven by independent uniform
  integer choices and the limit of its normalized expectation. This file
  contains no proof.
*)

theory putnam_2024_b4
  imports Complex_Main
begin

definition putnam_2024_b4_sigma_algebra ::
    "'a set set \<Rightarrow> bool" where
  "putnam_2024_b4_sigma_algebra E \<longleftrightarrow>
    UNIV \<in> E \<and>
    (\<forall>A\<in>E. UNIV - A \<in> E) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>i. A i \<in> E) \<longrightarrow> (\<Union>i. A i) \<in> E)"

definition putnam_2024_b4_probability_measure ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> bool" where
  "putnam_2024_b4_probability_measure E P \<longleftrightarrow>
    putnam_2024_b4_sigma_algebra E \<and>
    P {} = 0 \<and>
    P UNIV = 1 \<and>
    (\<forall>A\<in>E. 0 \<le> P A) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>i. A i \<in> E) \<longrightarrow>
      (\<forall>i j. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}) \<longrightarrow>
      P (\<Union>i. A i) = (\<Sum>i. P (A i)))"

definition putnam_2024_b4_int_random_variable ::
    "'a set set \<Rightarrow> ('a \<Rightarrow> int) \<Rightarrow> bool" where
  "putnam_2024_b4_int_random_variable E X \<longleftrightarrow>
    (\<forall>B :: int set. X -` B \<in> E)"

definition putnam_2024_b4_uniform_integer_choice ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow>
      nat \<Rightarrow> ('a \<Rightarrow> int) \<Rightarrow> bool" where
  "putnam_2024_b4_uniform_integer_choice E P n X \<longleftrightarrow>
    putnam_2024_b4_int_random_variable E X \<and>
    (\<forall>B :: int set.
      P (X -` B) =
        real (card (B \<inter> {1..int n})) / real n)"

definition putnam_2024_b4_mutually_independent ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow>
      ('i \<Rightarrow> 'a \<Rightarrow> int) \<Rightarrow> bool" where
  "putnam_2024_b4_mutually_independent E P X \<longleftrightarrow>
    (\<forall>i. putnam_2024_b4_int_random_variable E (X i)) \<and>
    (\<forall>J A.
      finite J \<longrightarrow>
      P (\<Inter>i\<in>J. X i -` A i) =
        (\<Prod>i\<in>J. P (X i -` A i)))"

definition putnam_2024_b4_expectation ::
    "('a set \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> int) \<Rightarrow> real" where
  "putnam_2024_b4_expectation P X =
    (\<Sum>z :: int. real_of_int z * P {\<omega>. X \<omega> = z})"

theorem putnam_2024_b4:
  fixes E :: "'a set set"
    and P :: "'a set \<Rightarrow> real"
    and m a :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> int"
  assumes probability_space:
      "putnam_2024_b4_probability_measure E P"
    and a_initial:
      "\<And>n. 0 < n \<Longrightarrow> a n 0 = (\<lambda>\<omega>. 1)"
    and m_uniform:
      "\<And>n k. 0 < n \<Longrightarrow>
        putnam_2024_b4_uniform_integer_choice E P n (m n k)"
    and a_recurrence:
      "\<And>n k \<omega>. 0 < n \<Longrightarrow>
        a n (Suc k) \<omega> =
          (if m n k \<omega> > a n k \<omega> then
             a n k \<omega> + 1
           else if m n k \<omega> = a n k \<omega> then
             a n k \<omega>
           else
             a n k \<omega> - 1)"
    and m_independent:
      "putnam_2024_b4_mutually_independent E P (case_prod m)"
  shows
    "((\<lambda>n. putnam_2024_b4_expectation P (a n n) / real n)
      \<longlongrightarrow> (1 - exp (-2)) / 2) at_top"
  sorry

end
