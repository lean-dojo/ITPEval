(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a3
  (putnambench__isabelle__putnam_2024_a3): among the increasing bijective
  fillings of a 3 by 2024 grid with 1 through 6072, some pair of positions is
  ordered in between one third and two thirds of the fillings. This file
  contains no proof.
*)

theory putnam_2024_a3
  imports Complex_Main
begin

definition putnam_2024_a3_domain :: "(nat \<times> nat) set" where
  "putnam_2024_a3_domain = {1..3} \<times> {1..2024}"

definition putnam_2024_a3_codomain :: "nat set" where
  "putnam_2024_a3_codomain = {1..6072}"

definition putnam_2024_a3_S :: "((nat \<times> nat) \<Rightarrow> nat) set" where
  "putnam_2024_a3_S =
    {T.
      bij_betw T putnam_2024_a3_domain putnam_2024_a3_codomain \<and>
      (\<forall>j\<in>{1..2024}.
        strict_mono_on {1..3} (\<lambda>i. T (i, j))) \<and>
      (\<forall>i\<in>{1..3}.
        strict_mono_on {1..2024} (\<lambda>j. T (i, j))) \<and>
      (\<forall>x. x \<notin> putnam_2024_a3_domain \<longrightarrow> T x = 0)}"

theorem putnam_2024_a3:
  shows
    "\<exists>a\<in>{1..3}. \<exists>b\<in>{1..2024}.
      \<exists>c\<in>{1..3}. \<exists>d\<in>{1..2024}.
        (rat_of_nat
            (card {T\<in>putnam_2024_a3_S. T (a, b) < T (c, d)}) /
          rat_of_nat (card putnam_2024_a3_S) :: rat)
        \<in> {1 / 3..2 / 3}"
  sorry

end
