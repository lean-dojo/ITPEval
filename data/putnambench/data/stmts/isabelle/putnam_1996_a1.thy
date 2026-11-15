(*
  Statement-only formalization of PutnamBench artifact putnam_1996_a1,
  concerning the least area of a rectangle that can pack every pair of
  positive squares whose areas sum to one. This file contains no proof.
*)

theory putnam_1996_a1
  imports Complex_Main
begin

definition putnam_1996_a1_solution :: real where
  "putnam_1996_a1_solution = (1 + sqrt 2) / 2"

definition putnam_1996_a1_packable ::
    "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "putnam_1996_a1_packable n1 n2 a1 a2 \<longleftrightarrow>
    n1 + n2 \<le> max a1 a2 \<and> max n1 n2 \<le> min a1 a2"

definition putnam_1996_a1_Aprop :: "real \<Rightarrow> bool" where
  "putnam_1996_a1_Aprop A \<longleftrightarrow>
    (\<forall>n1 n2 :: real.
      (n1 > 0 \<and> n2 > 0 \<and> n1 ^ 2 + n2 ^ 2 = 1) \<longrightarrow>
      (\<exists>a1 a2 :: real.
        a1 > 0 \<and> a2 > 0 \<and> a1 * a2 = A \<and>
        putnam_1996_a1_packable n1 n2 a1 a2))"

theorem putnam_1996_a1:
  shows
    "putnam_1996_a1_Aprop putnam_1996_a1_solution \<and>
     (\<forall>A :: real.
       putnam_1996_a1_Aprop A \<longrightarrow>
       A \<ge> putnam_1996_a1_solution)"
  sorry

end
