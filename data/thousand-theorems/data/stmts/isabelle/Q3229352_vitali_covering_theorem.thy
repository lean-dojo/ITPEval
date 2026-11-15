(*
  Statement-only formalization of the thousand-theorems corpus artifact Q3229352,
  "Vitali covering theorem": a fine family of closed sets in a second-countable
  pseudometric measure space, satisfying a uniform enlarged-ball measure bound,
  has a countable pairwise-disjoint subfamily covering the given set almost
  everywhere. This file contains no proof.
*)

theory Q3229352_vitali_covering_theorem
  imports "HOL-Analysis.Borel_Space" "HOL-Analysis.Measure_Space"
begin

definition q3229352_pseudometric ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q3229352_pseudometric d \<longleftrightarrow>
      (\<forall>x. d x x = 0) \<and>
      (\<forall>x y. 0 \<le> d x y) \<and>
      (\<forall>x y. d x y = d y x) \<and>
      (\<forall>x y z. d x z \<le> d x y + d y z)"

definition q3229352_ball ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a set"
  where
    "q3229352_ball d x radius = {y. d y x < radius}"

definition q3229352_cball ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a set"
  where
    "q3229352_cball d x radius = {y. d y x \<le> radius}"

definition q3229352_open ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q3229352_open d U \<longleftrightarrow>
      (\<forall>x \<in> U. \<exists>radius > 0. q3229352_ball d x radius \<subseteq> U)"

definition q3229352_closed ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q3229352_closed d A \<longleftrightarrow> q3229352_open d (- A)"

definition q3229352_interior ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where
    "q3229352_interior d A =
      {x. \<exists>radius > 0. q3229352_ball d x radius \<subseteq> A}"

definition q3229352_second_countable ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q3229352_second_countable d \<longleftrightarrow>
      (\<exists>basis :: 'a set set.
        countable basis \<and>
        (\<forall>A \<in> basis. q3229352_open d A) \<and>
        (\<forall>U x. q3229352_open d U \<longrightarrow> x \<in> U \<longrightarrow>
          (\<exists>A \<in> basis. x \<in> A \<and> A \<subseteq> U)))"

definition q3229352_opens_measurable ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a measure \<Rightarrow> bool"
  where
    "q3229352_opens_measurable d M \<longleftrightarrow>
      space M = UNIV \<and>
      (\<forall>U. q3229352_open d U \<longrightarrow> U \<in> sets M)"

definition q3229352_locally_finite ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a measure \<Rightarrow> bool"
  where
    "q3229352_locally_finite d M \<longleftrightarrow>
      (\<forall>x. \<exists>U. q3229352_open d U \<and> x \<in> U \<and>
        emeasure M U < \<infinity>)"

definition q3229352_outer_null ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "q3229352_outer_null M A \<longleftrightarrow>
      (\<exists>N \<in> sets M. A \<subseteq> N \<and> emeasure M N = 0)"

theorem vitali_covering_theorem:
  fixes d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
    and M :: "'a measure"
    and s :: "'a set"
    and t :: "'i set"
    and C :: real
    and r :: "'i \<Rightarrow> real"
    and c :: "'i \<Rightarrow> 'a"
    and B :: "'i \<Rightarrow> 'a set"
  assumes pseudometric:
      "q3229352_pseudometric d"
    and second_countable:
      "q3229352_second_countable d"
    and opens_measurable:
      "q3229352_opens_measurable d M"
    and locally_finite:
      "q3229352_locally_finite d M"
    and C_nonnegative:
      "0 \<le> C"
    and contained_in_ball:
      "\<And>a. a \<in> t \<Longrightarrow>
        B a \<subseteq> q3229352_cball d (c a) (r a)"
    and enlarged_ball_bound:
      "\<And>a. a \<in> t \<Longrightarrow>
        emeasure M (q3229352_cball d (c a) (3 * r a))
          \<le> ennreal C * emeasure M (B a)"
    and nonempty_interior:
      "\<And>a. a \<in> t \<Longrightarrow> q3229352_interior d (B a) \<noteq> {}"
    and closed:
      "\<And>a. a \<in> t \<Longrightarrow> q3229352_closed d (B a)"
    and fine:
      "\<And>x epsilon. x \<in> s \<Longrightarrow> 0 < epsilon \<Longrightarrow>
        \<exists>a \<in> t. r a \<le> epsilon \<and> c a = x"
  shows
      "\<exists>u \<subseteq> t.
        countable u \<and>
        pairwise (\<lambda>a b. disjnt (B a) (B b)) u \<and>
        q3229352_outer_null M (s - (\<Union>a\<in>u. B a))"
  sorry

end
