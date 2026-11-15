(*
  Statement-only formalization of thousand-theorems corpus artifact Q20971632
  (thousand-theorems__isabelle__Q20971632), "Lie's theorem": a finite nonzero
  triangularizable module of a solvable Lie algebra over a characteristic-zero
  field has a nonzero common weight vector. This file contains no proof.
*)

theory Q20971632_lie_s_theorem
  imports Main
begin

definition q20971632_char_zero ::
    "'k::field itself \<Rightarrow> bool" where
  "q20971632_char_zero TYPE('k) \<longleftrightarrow>
    (\<forall>m n :: nat.
      (of_nat m :: 'k) = of_nat n \<longrightarrow> m = n)"

definition q20971632_module ::
    "('k::field \<Rightarrow> 'a::ab_group_add \<Rightarrow> 'a) \<Rightarrow> bool" where
  "q20971632_module smul \<longleftrightarrow>
    (\<forall>x. smul 1 x = x) \<and>
    (\<forall>a b x. smul (a * b) x = smul a (smul b x)) \<and>
    (\<forall>a b x. smul (a + b) x = smul a x + smul b x) \<and>
    (\<forall>a x y. smul a (x + y) = smul a x + smul a y) \<and>
    (\<forall>x. smul 0 x = 0) \<and>
    (\<forall>a. smul a 0 = 0)"

definition q20971632_subspace ::
    "('k::field \<Rightarrow> 'a::ab_group_add \<Rightarrow> 'a) \<Rightarrow>
      'a set \<Rightarrow> bool" where
  "q20971632_subspace smul S \<longleftrightarrow>
    0 \<in> S \<and>
    (\<forall>x \<in> S. -x \<in> S) \<and>
    (\<forall>x \<in> S. \<forall>y \<in> S. x + y \<in> S) \<and>
    (\<forall>a. \<forall>x \<in> S. smul a x \<in> S)"

definition q20971632_span ::
    "('k::field \<Rightarrow> 'a::ab_group_add \<Rightarrow> 'a) \<Rightarrow>
      'a set \<Rightarrow> 'a set" where
  "q20971632_span smul A =
    \<Inter>{S. q20971632_subspace smul S \<and> A \<subseteq> S}"

definition q20971632_lie_algebra ::
    "('k::field \<Rightarrow> 'l::ab_group_add \<Rightarrow> 'l) \<Rightarrow>
      ('l \<Rightarrow> 'l \<Rightarrow> 'l) \<Rightarrow> bool" where
  "q20971632_lie_algebra smul bracket \<longleftrightarrow>
    (\<forall>x y z. bracket (x + y) z = bracket x z + bracket y z) \<and>
    (\<forall>x y z. bracket x (y + z) = bracket x y + bracket x z) \<and>
    (\<forall>x. bracket x x = 0) \<and>
    (\<forall>x y z.
      bracket x (bracket y z) =
        bracket (bracket x y) z + bracket y (bracket x z)) \<and>
    (\<forall>a x y. bracket x (smul a y) = smul a (bracket x y))"

definition q20971632_lie_module ::
    "('k::field \<Rightarrow> 'l::ab_group_add \<Rightarrow> 'l) \<Rightarrow>
      ('k \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v) \<Rightarrow>
      ('l \<Rightarrow> 'l \<Rightarrow> 'l) \<Rightarrow>
      ('l \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool" where
  "q20971632_lie_module smulL smulV bracket act \<longleftrightarrow>
    (\<forall>x y v. act (x + y) v = act x v + act y v) \<and>
    (\<forall>x v w. act x (v + w) = act x v + act x w) \<and>
    (\<forall>x y v.
      act x (act y v) = act (bracket x y) v + act y (act x v)) \<and>
    (\<forall>a x v. act (smulL a x) v = smulV a (act x v)) \<and>
    (\<forall>a x v. act x (smulV a v) = smulV a (act x v))"

primrec q20971632_derived_series ::
    "('k::field \<Rightarrow> 'l::ab_group_add \<Rightarrow> 'l) \<Rightarrow>
      ('l \<Rightarrow> 'l \<Rightarrow> 'l) \<Rightarrow> nat \<Rightarrow> 'l set" where
  "q20971632_derived_series smul bracket 0 = UNIV"
| "q20971632_derived_series smul bracket (Suc n) =
    q20971632_span smul
      {z. \<exists>x \<in> q20971632_derived_series smul bracket n.
        \<exists>y \<in> q20971632_derived_series smul bracket n.
          z = bracket x y}"

definition q20971632_solvable ::
    "('k::field \<Rightarrow> 'l::ab_group_add \<Rightarrow> 'l) \<Rightarrow>
      ('l \<Rightarrow> 'l \<Rightarrow> 'l) \<Rightarrow> bool" where
  "q20971632_solvable smul bracket \<longleftrightarrow>
    (\<exists>n. q20971632_derived_series smul bracket n = {0})"

definition q20971632_finite_module ::
    "('k::field \<Rightarrow> 'a::ab_group_add \<Rightarrow> 'a) \<Rightarrow> bool" where
  "q20971632_finite_module smul \<longleftrightarrow>
    (\<exists>B. finite B \<and> q20971632_span smul B = UNIV)"

primrec q20971632_iterate ::
    "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "q20971632_iterate f 0 v = v"
| "q20971632_iterate f (Suc n) v =
    f (q20971632_iterate f n v)"

definition q20971632_triangularizable ::
    "('k::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v) \<Rightarrow>
      ('l \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool" where
  "q20971632_triangularizable smul act \<longleftrightarrow>
    (\<forall>x.
      q20971632_span smul
        {v. \<exists>mu n.
          q20971632_iterate
            (\<lambda>w. act x w - smul mu w) n v = 0}
        = UNIV)"

definition q20971632_linear_functional ::
    "('k::field \<Rightarrow> 'l::ab_group_add \<Rightarrow> 'l) \<Rightarrow>
      ('l \<Rightarrow> 'k) \<Rightarrow> bool" where
  "q20971632_linear_functional smul chi \<longleftrightarrow>
    chi 0 = 0 \<and>
    (\<forall>x y. chi (x + y) = chi x + chi y) \<and>
    (\<forall>a x. chi (smul a x) = a * chi x)"

theorem q20971632_lies_theorem:
  fixes smulL :: "'k::field \<Rightarrow> 'l::ab_group_add \<Rightarrow> 'l"
    and smulV :: "'k \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v"
    and bracket :: "'l \<Rightarrow> 'l \<Rightarrow> 'l"
    and act :: "'l \<Rightarrow> 'v \<Rightarrow> 'v"
  assumes char_zero: "q20971632_char_zero TYPE('k)"
    and module_L: "q20971632_module smulL"
    and module_V: "q20971632_module smulV"
    and lie_algebra: "q20971632_lie_algebra smulL bracket"
    and lie_module: "q20971632_lie_module smulL smulV bracket act"
    and finite_V: "q20971632_finite_module smulV"
    and nontrivial_V: "\<exists>v :: 'v. v \<noteq> 0"
    and solvable_L: "q20971632_solvable smulL bracket"
    and triangularizable:
      "q20971632_triangularizable smulV act"
  shows "\<exists>chi :: 'l \<Rightarrow> 'k. \<exists>v :: 'v.
    q20971632_linear_functional smulL chi \<and>
    v \<noteq> 0 \<and>
    (\<forall>x. act x v = smulV (chi x) v)"
  sorry

end
