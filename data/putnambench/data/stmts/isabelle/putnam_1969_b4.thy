(*
  Statement-only formalization of PutnamBench artifact putnam_1969_b4,
  concerning a length-one continuous plane curve covered by a rectangle of
  area one quarter. This file contains no proof.
*)

theory putnam_1969_b4
  imports Complex_Main
begin

definition putnam_1969_b4_partition :: "real list \<Rightarrow> bool" where
  "putnam_1969_b4_partition xs \<longleftrightarrow>
    xs \<noteq> [] \<and>
    hd xs = 0 \<and>
    last xs = 1 \<and>
    sorted xs \<and>
    set xs \<subseteq> {0..1}"

definition putnam_1969_b4_partition_length ::
    "(real \<Rightarrow> complex) \<Rightarrow> real list \<Rightarrow> real" where
  "putnam_1969_b4_partition_length \<Gamma> xs =
    (\<Sum>i<length xs - 1. dist (\<Gamma> (xs ! i)) (\<Gamma> (xs ! (Suc i))))"

definition putnam_1969_b4_bounded_variation ::
    "(real \<Rightarrow> complex) \<Rightarrow> bool" where
  "putnam_1969_b4_bounded_variation \<Gamma> \<longleftrightarrow>
    (\<exists>B. \<forall>xs.
      putnam_1969_b4_partition xs \<longrightarrow>
      putnam_1969_b4_partition_length \<Gamma> xs \<le> B)"

definition putnam_1969_b4_curve_length ::
    "(real \<Rightarrow> complex) \<Rightarrow> real" where
  "putnam_1969_b4_curve_length \<Gamma> =
    Sup {putnam_1969_b4_partition_length \<Gamma> xs | xs.
      putnam_1969_b4_partition xs}"

definition putnam_1969_b4_in_convex_hull4 ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow>
      complex \<Rightarrow> bool" where
  "putnam_1969_b4_in_convex_hull4 p a b c d \<longleftrightarrow>
    (\<exists>wa wb wc wd :: real.
      0 \<le> wa \<and> 0 \<le> wb \<and> 0 \<le> wc \<and> 0 \<le> wd \<and>
      wa + wb + wc + wd = 1 \<and>
      p = of_real wa * a + of_real wb * b +
          of_real wc * c + of_real wd * d)"

definition putnam_1969_b4_right_angle ::
    "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> bool" where
  "putnam_1969_b4_right_angle a b c \<longleftrightarrow>
    Re (cnj (a - b) * (c - b)) = 0"

theorem putnam_1969_b4:
  fixes \<Gamma> :: "real \<Rightarrow> complex"
  assumes \<Gamma>_cts: "continuous_on {0..1} \<Gamma>"
    and \<Gamma>_length:
      "putnam_1969_b4_bounded_variation \<Gamma> \<and>
       putnam_1969_b4_curve_length \<Gamma> = 1"
  shows "\<exists>a b c d :: complex.
    (\<forall>t\<in>{0..1}. putnam_1969_b4_in_convex_hull4 (\<Gamma> t) a b c d) \<and>
    dist a b * dist b c = (1 / 4 :: real) \<and>
    putnam_1969_b4_right_angle a b c \<and>
    putnam_1969_b4_right_angle b c d \<and>
    putnam_1969_b4_right_angle c d a \<and>
    putnam_1969_b4_right_angle d a b"
  sorry

end
