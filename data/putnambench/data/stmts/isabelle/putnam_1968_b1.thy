(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b1,
  concerning the probabilities that the minimum and maximum of two
  finitely supported integer-valued random variables equal a fixed integer.
  This file contains no proof.
*)

theory putnam_1968_b1
  imports Complex_Main
begin

definition putnam_1968_b1_solution :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "putnam_1968_b1_solution \<equiv> \<lambda>a b c. a + b - c"

definition putnam_1968_b1_probability_space ::
    "'a set set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> bool" where
  "putnam_1968_b1_probability_space A P \<longleftrightarrow>
    {} \<in> A \<and>
    UNIV \<in> A \<and>
    (\<forall>S\<in>A. UNIV - S \<in> A) \<and>
    (\<forall>F :: nat \<Rightarrow> 'a set.
      (\<forall>n. F n \<in> A) \<longrightarrow> (\<Union>n. F n) \<in> A) \<and>
    P {} = 0 \<and>
    P UNIV = 1 \<and>
    (\<forall>S\<in>A. 0 \<le> P S) \<and>
    (\<forall>F :: nat \<Rightarrow> 'a set.
      (\<forall>n. F n \<in> A) \<longrightarrow>
      (\<forall>i j. i \<noteq> j \<longrightarrow> F i \<inter> F j = {}) \<longrightarrow>
      (\<lambda>n. P (F n)) sums P (\<Union>n. F n))"

theorem putnam_1968_b1:
  fixes A :: "'a set set"
    and P :: "'a set \<Rightarrow> real"
    and X Y :: "'a \<Rightarrow> int"
    and k :: int
  assumes hP: "putnam_1968_b1_probability_space A P"
    and hX: "\<forall>B :: int set. {\<omega>. X \<omega> \<in> B} \<in> A"
    and hY: "\<forall>B :: int set. {\<omega>. Y \<omega> \<in> B} \<in> A"
    and hX_finite: "finite (X ` UNIV)"
    and hY_finite: "finite (Y ` UNIV)"
  shows "P {\<omega>. min (X \<omega>) (Y \<omega>) = k} =
    putnam_1968_b1_solution
      (P {\<omega>. X \<omega> = k})
      (P {\<omega>. Y \<omega> = k})
      (P {\<omega>. max (X \<omega>) (Y \<omega>) = k})"
  sorry

end
