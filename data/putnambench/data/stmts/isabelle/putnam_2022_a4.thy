(*
  Statement-only formalization of PutnamBench artifact putnam_2022_a4,
  concerning the expected value of a weighted sum of independent uniform
  random variables stopped at their first increase. This file contains no proof.
*)

theory putnam_2022_a4
  imports Complex_Main
begin

definition sigma_algebra_on_UNIV :: "'a set set \<Rightarrow> bool" where
  "sigma_algebra_on_UNIV E \<longleftrightarrow>
    UNIV \<in> E \<and>
    (\<forall>A\<in>E. UNIV - A \<in> E) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>n. A n \<in> E) \<longrightarrow> (\<Union>n. A n) \<in> E)"

definition real_borel_sets :: "real set set" where
  "real_borel_sets =
    \<Inter>{E :: real set set.
      sigma_algebra_on_UNIV E \<and> {U. open U} \<subseteq> E}"

definition probability_measure_on ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> bool" where
  "probability_measure_on E P \<longleftrightarrow>
    sigma_algebra_on_UNIV E \<and>
    P {} = 0 \<and>
    P UNIV = 1 \<and>
    (\<forall>A\<in>E. 0 \<le> P A) \<and>
    (\<forall>A :: nat \<Rightarrow> 'a set.
      (\<forall>n. A n \<in> E) \<longrightarrow>
      (\<forall>m n. m \<noteq> n \<longrightarrow> A m \<inter> A n = {}) \<longrightarrow>
      P (\<Union>n. A n) = (\<Sum>n. P (A n)))"

definition real_random_variable ::
    "'a set set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "real_random_variable E f \<longleftrightarrow>
    (\<forall>B\<in>real_borel_sets. f -` B \<in> E)"

definition uniform_on_unit_interval ::
    "('a set \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "uniform_on_unit_interval P f \<longleftrightarrow>
    (\<forall>x. P {\<omega>. f \<omega> \<le> x} =
      (if x < 0 then 0 else if x \<le> 1 then x else 1))"

definition mutually_independent_real_random_variables ::
    "('a set \<Rightarrow> real) \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "mutually_independent_real_random_variables P X \<longleftrightarrow>
    (\<forall>J A.
      finite J \<longrightarrow>
      (\<forall>j\<in>J. A j \<in> real_borel_sets) \<longrightarrow>
      P (\<Inter>j\<in>J. X j -` A j) =
        (\<Prod>j\<in>J. P (X j -` A j)))"

definition simple_event_measurable ::
    "'a set set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "simple_event_measurable E g \<longleftrightarrow>
    finite (range g) \<and> (\<forall>y. {\<omega>. g \<omega> = y} \<in> E)"

definition simple_expectation ::
    "('a set \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "simple_expectation P g =
    (\<Sum>y\<in>range g. y * P {\<omega>. g \<omega> = y})"

definition nonnegative_expectation ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow>
      ('a \<Rightarrow> real) \<Rightarrow> real" where
  "nonnegative_expectation E P f =
    Sup {simple_expectation P g | g.
      simple_event_measurable E g \<and>
      (\<forall>\<omega>. 0 \<le> g \<omega> \<and> g \<omega> \<le> f \<omega>)}"

definition expectation ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow>
      ('a \<Rightarrow> real) \<Rightarrow> real" where
  "expectation E P f =
    nonnegative_expectation E P (\<lambda>\<omega>. max (f \<omega>) 0) -
    nonnegative_expectation E P (\<lambda>\<omega>. max (- f \<omega>) 0)"

theorem putnam_2022_a4:
  fixes E :: "'a set set"
    and P :: "'a set \<Rightarrow> real"
    and X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
    and k :: "'a \<Rightarrow> nat set"
    and S :: "'a \<Rightarrow> real"
  assumes probability_space: "probability_measure_on E P"
    and X_measurable: "\<And>i. real_random_variable E (X i)"
    and X_uniform: "\<And>i. uniform_on_unit_interval P (X i)"
    and X_independent: "mutually_independent_real_random_variables P X"
    and k_def:
      "\<And>\<omega>. k \<omega> =
        Sup {s :: nat set.
          \<exists>m. s = {..m} \<and>
            (\<forall>l<m. X l \<omega> > X (Suc l) \<omega>)}"
    and S_def:
      "\<And>\<omega>. S \<omega> =
        (\<Sum>i. if i \<in> k \<omega>
          then X i \<omega> / (2 :: real) ^ Suc i
          else 0)"
  shows "expectation E P S = 2 * exp (1 / 2) - 3"
  sorry

end
