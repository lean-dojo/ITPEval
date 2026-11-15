(*
  Statement-only formalization of thousand-theorems corpus artifact Q537618,
  "Banach–Alaoglu theorem": over a proper nontrivially normed field, the polar
  of a neighborhood of zero in a seminormed vector space is compact in the
  weak-star topology of its continuous dual. This file contains no proof.
*)

theory Q537618_banach_alaoglu_theorem
  imports Complex_Main
begin

definition q537618_topspace :: "'a set set \<Rightarrow> 'a set" where
  "q537618_topspace T = \<Union>T"

definition q537618_compactin :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q537618_compactin T K \<longleftrightarrow>
    K \<subseteq> q537618_topspace T \<and>
    (\<forall>C. C \<subseteq> T \<longrightarrow> K \<subseteq> \<Union>C \<longrightarrow>
      (\<exists>F \<subseteq> C. finite F \<and> K \<subseteq> \<Union>F))"

definition q537618_nontrivially_normed_field ::
    "('k::field \<Rightarrow> real) \<Rightarrow> bool" where
  "q537618_nontrivially_normed_field knorm \<longleftrightarrow>
    knorm 0 = 0 \<and>
    (\<forall>a. 0 \<le> knorm a) \<and>
    (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
    (\<forall>a. knorm (-a) = knorm a) \<and>
    (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
    (\<forall>a b. knorm (a * b) = knorm a * knorm b) \<and>
    (\<exists>a. 1 < knorm a)"

definition q537618_field_open ::
    "('k::field \<Rightarrow> real) \<Rightarrow> 'k set \<Rightarrow> bool" where
  "q537618_field_open knorm U \<longleftrightarrow>
    (\<forall>a \<in> U. \<exists>epsilon > 0.
      \<forall>b. knorm (b - a) < epsilon \<longrightarrow> b \<in> U)"

definition q537618_field_topology ::
    "('k::field \<Rightarrow> real) \<Rightarrow> 'k set set" where
  "q537618_field_topology knorm = {U. q537618_field_open knorm U}"

definition q537618_proper_field ::
    "('k::field \<Rightarrow> real) \<Rightarrow> bool" where
  "q537618_proper_field knorm \<longleftrightarrow>
    (\<forall>a r. q537618_compactin (q537618_field_topology knorm)
      {b. knorm (b - a) \<le> r})"

definition q537618_seminormed_add_comm_group ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> bool" where
  "q537618_seminormed_add_comm_group enorm \<longleftrightarrow>
    enorm 0 = 0 \<and>
    (\<forall>x. 0 \<le> enorm x) \<and>
    (\<forall>x. enorm (-x) = enorm x) \<and>
    (\<forall>x y. enorm (x + y) \<le> enorm x + enorm y)"

definition q537618_normed_space ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q537618_normed_space knorm enorm scale \<longleftrightarrow>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>a x. enorm (scale a x) = knorm a * enorm x)"

definition q537618_continuous_linear ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     ('e \<Rightarrow> 'k) \<Rightarrow> bool" where
  "q537618_continuous_linear knorm enorm scale f \<longleftrightarrow>
    (\<forall>x y. f (x + y) = f x + f y) \<and>
    (\<forall>a x. f (scale a x) = a * f x) \<and>
    (\<forall>x epsilon. 0 < epsilon \<longrightarrow>
      (\<exists>delta > 0. \<forall>y.
        enorm (y - x) < delta \<longrightarrow>
        knorm (f y - f x) < epsilon))"

definition q537618_dual ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     ('e \<Rightarrow> 'k) set" where
  "q537618_dual knorm enorm scale =
    {f. q537618_continuous_linear knorm enorm scale f}"

definition q537618_weak_star_open ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     ('e \<Rightarrow> 'k) set \<Rightarrow> bool" where
  "q537618_weak_star_open knorm enorm scale U \<longleftrightarrow>
    U \<subseteq> q537618_dual knorm enorm scale \<and>
    (\<forall>f \<in> U. \<exists>J V.
      finite J \<and>
      (\<forall>x \<in> J. q537618_field_open knorm (V x)) \<and>
      (\<forall>x \<in> J. f x \<in> V x) \<and>
      {g. g \<in> q537618_dual knorm enorm scale \<and>
        (\<forall>x \<in> J. g x \<in> V x)} \<subseteq> U)"

definition q537618_weak_star_topology ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     ('e \<Rightarrow> 'k) set set" where
  "q537618_weak_star_topology knorm enorm scale =
    {U. q537618_weak_star_open knorm enorm scale U}"

definition q537618_polar ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
     ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
     ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
     'e set \<Rightarrow> ('e \<Rightarrow> 'k) set" where
  "q537618_polar knorm enorm scale s =
    {f. f \<in> q537618_dual knorm enorm scale \<and>
      (\<forall>x \<in> s. knorm (f x) \<le> 1)}"

definition q537618_neighborhood_zero ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q537618_neighborhood_zero enorm s \<longleftrightarrow>
    (\<exists>epsilon > 0. {x. enorm x < epsilon} \<subseteq> s)"

theorem banach_alaoglu:
  fixes knorm :: "'k::field \<Rightarrow> real"
    and enorm :: "'e::ab_group_add \<Rightarrow> real"
    and scale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and s :: "'e set"
  assumes "q537618_nontrivially_normed_field knorm"
    and "q537618_proper_field knorm"
    and "q537618_seminormed_add_comm_group enorm"
    and "q537618_normed_space knorm enorm scale"
    and "q537618_neighborhood_zero enorm s"
  shows "q537618_compactin
    (q537618_weak_star_topology knorm enorm scale)
    (q537618_polar knorm enorm scale s)"
  sorry

end
