(*
  Statement-only formalization of thousand-theorems corpus artifact Q642620,
  "Krein–Milman theorem": every compact convex subset of a Hausdorff locally
  convex real topological vector space is the closure of the convex hull of
  its extreme points. This file contains no proof.
*)

theory Q642620_krein_milman_theorem
  imports Complex_Main
begin

definition q642620_module ::
    "(real \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q642620_module scale \<longleftrightarrow>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>x. scale 1 x = x)"

definition q642620_is_topology :: "'e set set \<Rightarrow> bool" where
  "q642620_is_topology T \<longleftrightarrow>
    {} \<in> T \<and>
    UNIV \<in> T \<and>
    (\<forall>K. K \<subseteq> T \<longrightarrow> \<Union>K \<in> T) \<and>
    (\<forall>U \<in> T. \<forall>V \<in> T. U \<inter> V \<in> T)"

definition q642620_hausdorff :: "'e set set \<Rightarrow> bool" where
  "q642620_hausdorff T \<longleftrightarrow>
    (\<forall>x y. x \<noteq> y \<longrightarrow>
      (\<exists>U \<in> T. \<exists>V \<in> T.
        x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))"

definition q642620_topological_add_group ::
    "'e::ab_group_add set set \<Rightarrow> bool" where
  "q642620_topological_add_group T \<longleftrightarrow>
    (\<forall>x y U.
      U \<in> T \<longrightarrow>
      x + y \<in> U \<longrightarrow>
      (\<exists>V \<in> T. \<exists>W \<in> T.
        x \<in> V \<and> y \<in> W \<and>
        (\<forall>v \<in> V. \<forall>w \<in> W. v + w \<in> U))) \<and>
    (\<forall>x U.
      U \<in> T \<longrightarrow>
      -x \<in> U \<longrightarrow>
      (\<exists>V \<in> T. x \<in> V \<and> (\<forall>y \<in> V. -y \<in> U)))"

definition q642620_continuous_smul ::
    "(real \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> 'e set set \<Rightarrow> bool" where
  "q642620_continuous_smul scale T \<longleftrightarrow>
    (\<forall>a x U.
      U \<in> T \<longrightarrow>
      scale a x \<in> U \<longrightarrow>
      (\<exists>A. open A \<and> a \<in> A \<and>
        (\<exists>V \<in> T. x \<in> V \<and>
          (\<forall>b \<in> A. \<forall>y \<in> V. scale b y \<in> U))))"

definition q642620_convex ::
    "(real \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> bool" where
  "q642620_convex scale S \<longleftrightarrow>
    (\<forall>x \<in> S. \<forall>y \<in> S. \<forall>a \<ge> 0. \<forall>b \<ge> 0.
      a + b = 1 \<longrightarrow> scale a x + scale b y \<in> S)"

definition q642620_neighborhood ::
    "'e set set \<Rightarrow> 'e \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q642620_neighborhood T x U \<longleftrightarrow>
    (\<exists>V \<in> T. x \<in> V \<and> V \<subseteq> U)"

definition q642620_locally_convex ::
    "(real \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set set \<Rightarrow> bool" where
  "q642620_locally_convex scale T \<longleftrightarrow>
    (\<forall>x U.
      q642620_neighborhood T x U \<longrightarrow>
      (\<exists>V.
        q642620_neighborhood T x V \<and>
        q642620_convex scale V \<and>
        V \<subseteq> U))"

definition q642620_compact ::
    "'e set set \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q642620_compact T S \<longleftrightarrow>
    (\<forall>C.
      C \<subseteq> T \<longrightarrow>
      S \<subseteq> \<Union>C \<longrightarrow>
      (\<exists>D \<subseteq> C. finite D \<and> S \<subseteq> \<Union>D))"

definition q642620_closure ::
    "'e set set \<Rightarrow> 'e set \<Rightarrow> 'e set" where
  "q642620_closure T S =
    {x. \<forall>U \<in> T. x \<in> U \<longrightarrow> U \<inter> S \<noteq> {}}"

definition q642620_convex_hull ::
    "(real \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> 'e set" where
  "q642620_convex_hull scale S =
    {x. \<forall>C.
      S \<subseteq> C \<longrightarrow>
      q642620_convex scale C \<longrightarrow>
      x \<in> C}"

definition q642620_extreme_points ::
    "(real \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      'e set \<Rightarrow> 'e set" where
  "q642620_extreme_points scale S =
    {x. x \<in> S \<and>
      (\<forall>y \<in> S. \<forall>z \<in> S. \<forall>a > 0. \<forall>b > 0.
        a + b = 1 \<longrightarrow>
        x = scale a y + scale b z \<longrightarrow>
        y = x \<and> z = x)}"

theorem closure_convexHull_extremePoints:
  fixes scale :: "real \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e"
    and T :: "'e set set"
    and S :: "'e set"
  assumes module: "q642620_module scale"
    and topology: "q642620_is_topology T"
    and hausdorff: "q642620_hausdorff T"
    and topological_add_group: "q642620_topological_add_group T"
    and continuous_smul: "q642620_continuous_smul scale T"
    and locally_convex: "q642620_locally_convex scale T"
    and compact: "q642620_compact T S"
    and convex: "q642620_convex scale S"
  shows "q642620_closure T
    (q642620_convex_hull scale (q642620_extreme_points scale S)) = S"
  sorry

end
