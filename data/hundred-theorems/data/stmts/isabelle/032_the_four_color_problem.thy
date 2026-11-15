(*
  Statement-only formalization of Hundred Theorems item 032, "The Four Color
  Problem". It states that finite and arbitrary simple maps over every modeled
  real plane admit a coloring with at most four colors. This file contains no
  proof.
*)

theory Four_Color_Problem
  imports Main
begin

type_synonym 'a fc_point = "'a \<times> 'a"
type_synonym 'a fc_region = "'a fc_point \<Rightarrow> bool"
type_synonym 'a fc_plane_map = "'a fc_point \<Rightarrow> 'a fc_region"
type_synonym 'a fc_interval = "'a \<times> 'a"
type_synonym 'a fc_rectangle = "'a fc_interval \<times> 'a fc_interval"

definition fc_real_eq ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "fc_real_eq rle x y \<longleftrightarrow> rle x y \<and> rle y x"

definition fc_upper_bounds ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow>
      'a \<Rightarrow> bool" where
  "fc_upper_bounds rle E z \<longleftrightarrow> (\<forall>y. E y \<longrightarrow> rle y z)"

definition fc_downward_closure ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow>
      'a \<Rightarrow> bool" where
  "fc_downward_closure rle E x \<longleftrightarrow>
    (\<exists>y. E y \<and> rle x y)"

definition fc_has_supremum ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "fc_has_supremum rle E \<longleftrightarrow>
    (\<exists>x. E x) \<and> (\<exists>z. fc_upper_bounds rle E z)"

locale fc_real_model =
  fixes rle :: "'r \<Rightarrow> 'r \<Rightarrow> bool"
    and rsup :: "('r \<Rightarrow> bool) \<Rightarrow> 'r"
    and radd :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
    and rzero :: "'r"
    and ropp :: "'r \<Rightarrow> 'r"
    and rmul :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
    and rone :: "'r"
    and rinv :: "'r \<Rightarrow> 'r"
  assumes rle_reflexive: "\<And>x. rle x x"
    and rle_transitive: "\<And>x y z. rle x y \<Longrightarrow> rle y z \<Longrightarrow> rle x z"
    and rsup_upper_bound:
      "\<And>E. fc_has_supremum rle E \<Longrightarrow> fc_upper_bounds rle E (rsup E)"
    and rsup_total:
      "\<And>E x. fc_has_supremum rle E \<Longrightarrow>
        fc_downward_closure rle E x \<or> rle (rsup E) x"
    and radd_monotone:
      "\<And>x y z. rle y z \<Longrightarrow> rle (radd x y) (radd x z)"
    and radd_commutative:
      "\<And>x y. fc_real_eq rle (radd x y) (radd y x)"
    and radd_associative:
      "\<And>x y z. fc_real_eq rle (radd x (radd y z)) (radd (radd x y) z)"
    and radd_zero_left:
      "\<And>x. fc_real_eq rle (radd rzero x) x"
    and radd_opposite_right:
      "\<And>x. fc_real_eq rle (radd x (ropp x)) rzero"
    and rmul_monotone:
      "\<And>x y z. rle rzero x \<Longrightarrow> rle y z \<Longrightarrow>
        rle (rmul x y) (rmul x z)"
    and rmul_commutative:
      "\<And>x y. fc_real_eq rle (rmul x y) (rmul y x)"
    and rmul_associative:
      "\<And>x y z. fc_real_eq rle (rmul x (rmul y z)) (rmul (rmul x y) z)"
    and rmul_distributive_right:
      "\<And>x y z. fc_real_eq rle (rmul x (radd y z))
        (radd (rmul x y) (rmul x z))"
    and rmul_one_left:
      "\<And>x. fc_real_eq rle (rmul rone x) x"
    and rmul_inverse_right:
      "\<And>x. \<not> fc_real_eq rle x rzero \<Longrightarrow>
        fc_real_eq rle (rmul x (rinv x)) rone"
    and rone_nonzero:
      "\<not> fc_real_eq rle rone rzero"
begin

definition fc_in_interval :: "'r fc_interval \<Rightarrow> 'r \<Rightarrow> bool" where
  "fc_in_interval s t \<longleftrightarrow>
    \<not> rle t (fst s) \<and> \<not> rle (snd s) t"

definition fc_in_rectangle :: "'r fc_rectangle \<Rightarrow> 'r fc_region" where
  "fc_in_rectangle rect p \<longleftrightarrow>
    fc_in_interval (fst rect) (fst p) \<and>
    fc_in_interval (snd rect) (snd p)"

definition fc_region_union :: "'r fc_region \<Rightarrow> 'r fc_region \<Rightarrow> 'r fc_region" where
  "fc_region_union r1 r2 p \<longleftrightarrow> r1 p \<or> r2 p"

definition fc_region_intersection ::
    "'r fc_region \<Rightarrow> 'r fc_region \<Rightarrow> 'r fc_region" where
  "fc_region_intersection r1 r2 p \<longleftrightarrow> r1 p \<and> r2 p"

definition fc_nonempty_region :: "'r fc_region \<Rightarrow> bool" where
  "fc_nonempty_region r \<longleftrightarrow> (\<exists>p. r p)"

definition fc_subregion :: "'r fc_region \<Rightarrow> 'r fc_region \<Rightarrow> bool" where
  "fc_subregion r1 r2 \<longleftrightarrow> (\<forall>p. r1 p \<longrightarrow> r2 p)"

definition fc_regions_meet :: "'r fc_region \<Rightarrow> 'r fc_region \<Rightarrow> bool" where
  "fc_regions_meet r1 r2 \<longleftrightarrow>
    fc_nonempty_region (fc_region_intersection r1 r2)"

definition fc_plain_map :: "'r fc_plane_map \<Rightarrow> bool" where
  "fc_plain_map m \<longleftrightarrow>
    (\<forall>p q. m p q \<longrightarrow> m q p) \<and>
    (\<forall>p q. m p q \<longrightarrow> fc_subregion (m q) (m p))"

definition fc_cover :: "'r fc_plane_map \<Rightarrow> 'r fc_region" where
  "fc_cover m p \<longleftrightarrow> m p p"

definition fc_submap :: "'r fc_plane_map \<Rightarrow> 'r fc_plane_map \<Rightarrow> bool" where
  "fc_submap m1 m2 \<longleftrightarrow> (\<forall>p. fc_subregion (m1 p) (m2 p))"

definition fc_at_most_regions :: "nat \<Rightarrow> 'r fc_plane_map \<Rightarrow> bool" where
  "fc_at_most_regions n m \<longleftrightarrow>
    (\<exists>representatives :: nat \<Rightarrow> 'r fc_point.
      \<forall>p. fc_cover m p \<longrightarrow>
        (\<exists>i. i < n \<and> m (representatives i) p))"

definition fc_open_region :: "'r fc_region \<Rightarrow> bool" where
  "fc_open_region r \<longleftrightarrow>
    (\<forall>p. r p \<longrightarrow>
      (\<exists>rect. fc_in_rectangle rect p \<and>
        fc_subregion (fc_in_rectangle rect) r))"

definition fc_closure :: "'r fc_region \<Rightarrow> 'r fc_region" where
  "fc_closure r p \<longleftrightarrow>
    (\<forall>u. fc_open_region u \<longrightarrow> u p \<longrightarrow> fc_regions_meet r u)"

definition fc_connected_region :: "'r fc_region \<Rightarrow> bool" where
  "fc_connected_region r \<longleftrightarrow>
    (\<forall>u v. fc_open_region u \<longrightarrow> fc_open_region v \<longrightarrow>
      fc_subregion r (fc_region_union u v) \<longrightarrow>
      fc_regions_meet u r \<longrightarrow> fc_regions_meet v r \<longrightarrow>
      fc_regions_meet u v)"

definition fc_simple_map :: "'r fc_plane_map \<Rightarrow> bool" where
  "fc_simple_map m \<longleftrightarrow>
    fc_plain_map m \<and>
    (\<forall>p. fc_open_region (m p)) \<and>
    (\<forall>p. fc_connected_region (m p))"

definition fc_finite_simple_map :: "'r fc_plane_map \<Rightarrow> bool" where
  "fc_finite_simple_map m \<longleftrightarrow>
    fc_simple_map m \<and> (\<exists>n. fc_at_most_regions n m)"

definition fc_border ::
    "'r fc_plane_map \<Rightarrow> 'r fc_point \<Rightarrow> 'r fc_point \<Rightarrow>
      'r fc_region" where
  "fc_border m p q =
    fc_region_intersection (fc_closure (m p)) (fc_closure (m q))"

definition fc_corner_map ::
    "'r fc_plane_map \<Rightarrow> 'r fc_point \<Rightarrow> 'r fc_plane_map" where
  "fc_corner_map m p q r \<longleftrightarrow> m q r \<and> fc_closure (m q) p"

definition fc_not_corner :: "'r fc_plane_map \<Rightarrow> 'r fc_region" where
  "fc_not_corner m p \<longleftrightarrow> fc_at_most_regions 2 (fc_corner_map m p)"

definition fc_adjacent ::
    "'r fc_plane_map \<Rightarrow> 'r fc_point \<Rightarrow> 'r fc_point \<Rightarrow> bool" where
  "fc_adjacent m p q \<longleftrightarrow>
    \<not> m p q \<and> fc_regions_meet (fc_not_corner m) (fc_border m p q)"

definition fc_coloring ::
    "'r fc_plane_map \<Rightarrow> 'r fc_plane_map \<Rightarrow> bool" where
  "fc_coloring m k \<longleftrightarrow>
    fc_plain_map k \<and>
    fc_subregion (fc_cover k) (fc_cover m) \<and>
    fc_submap m k \<and>
    (\<forall>p q. fc_adjacent m p q \<longrightarrow> \<not> k p q)"

definition fc_colorable_with :: "nat \<Rightarrow> 'r fc_plane_map \<Rightarrow> bool" where
  "fc_colorable_with n m \<longleftrightarrow>
    (\<exists>k. fc_coloring m k \<and> fc_at_most_regions n k)"

theorem four_color_finite:
  fixes m :: "'r fc_plane_map"
  assumes "fc_finite_simple_map m"
  shows "fc_colorable_with 4 m"
  sorry

theorem four_color:
  fixes m :: "'r fc_plane_map"
  assumes "fc_simple_map m"
  shows "fc_colorable_with 4 m"
  sorry

end

end
