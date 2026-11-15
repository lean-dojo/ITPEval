(*
  Statement-only formalization of thousand-theorems corpus artifact Q213603
  (thousand-theorems__isabelle__Q213603), "Ceva's theorem": in a triangle over
  an arbitrary normed field and normed affine torsor, three concurrent cevians
  give a cyclic product of distance ratios equal to one. This file contains no
  proof.
*)

theory Q213603_ceva_s_theorem
  imports Complex_Main
begin

datatype q213603_fin3 = Q0 | Q1 | Q2

fun q213603_succ :: "q213603_fin3 \<Rightarrow> q213603_fin3" where
  "q213603_succ Q0 = Q1"
| "q213603_succ Q1 = Q2"
| "q213603_succ Q2 = Q0"

definition q213603_succ2 :: "q213603_fin3 \<Rightarrow> q213603_fin3" where
  "q213603_succ2 i = q213603_succ (q213603_succ i)"

definition q213603_sum3_field ::
    "(q213603_fin3 \<Rightarrow> 'k::field) \<Rightarrow> 'k" where
  "q213603_sum3_field f = f Q0 + f Q1 + f Q2"

definition q213603_sum3_vector ::
    "(q213603_fin3 \<Rightarrow> 'v::ab_group_add) \<Rightarrow> 'v" where
  "q213603_sum3_vector f = f Q0 + f Q1 + f Q2"

definition q213603_prod3 ::
    "(q213603_fin3 \<Rightarrow> real) \<Rightarrow> real" where
  "q213603_prod3 f = f Q0 * f Q1 * f Q2"

definition q213603_normed_field ::
    "('k::field \<Rightarrow> real) \<Rightarrow> bool" where
  "q213603_normed_field knorm \<longleftrightarrow>
    knorm 0 = 0 \<and>
    (\<forall>a. 0 \<le> knorm a) \<and>
    (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
    (\<forall>a. knorm (-a) = knorm a) \<and>
    (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
    (\<forall>a b. knorm (a * b) = knorm a * knorm b)"

definition q213603_seminormed_add_comm_group ::
    "('v::ab_group_add \<Rightarrow> real) \<Rightarrow> bool" where
  "q213603_seminormed_add_comm_group vnorm \<longleftrightarrow>
    vnorm 0 = 0 \<and>
    (\<forall>v. 0 \<le> vnorm v) \<and>
    (\<forall>v. vnorm (-v) = vnorm v) \<and>
    (\<forall>v w. vnorm (v + w) \<le> vnorm v + vnorm w)"

definition q213603_normed_space ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
      ('v::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> bool" where
  "q213603_normed_space knorm vnorm smul \<longleftrightarrow>
    (\<forall>a v w. smul a (v + w) = smul a v + smul a w) \<and>
    (\<forall>a b v. smul (a + b) v = smul a v + smul b v) \<and>
    (\<forall>a b v. smul (a * b) v = smul a (smul b v)) \<and>
    (\<forall>v. smul 1 v = v) \<and>
    (\<forall>a v. vnorm (smul a v) = knorm a * vnorm v)"

definition q213603_normed_add_torsor ::
    "('v::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('v \<Rightarrow> 'p::metric_space \<Rightarrow> 'p) \<Rightarrow>
      ('p \<Rightarrow> 'p \<Rightarrow> 'v) \<Rightarrow> bool" where
  "q213603_normed_add_torsor vnorm vadd vsub \<longleftrightarrow>
    (\<forall>p. vadd 0 p = p) \<and>
    (\<forall>v w p. vadd (v + w) p = vadd v (vadd w p)) \<and>
    (\<forall>p q. vadd (vsub p q) q = p) \<and>
    (\<forall>v p. vsub (vadd v p) p = v) \<and>
    (\<forall>p q. dist p q = vnorm (vsub p q))"

definition q213603_affine_independent_triangle ::
    "('k::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v) \<Rightarrow>
      ('p \<Rightarrow> 'p \<Rightarrow> 'v) \<Rightarrow>
      (q213603_fin3 \<Rightarrow> 'p) \<Rightarrow> bool" where
  "q213603_affine_independent_triangle smul vsub points \<longleftrightarrow>
    (\<forall>w :: q213603_fin3 \<Rightarrow> 'k.
      q213603_sum3_field w = 0 \<longrightarrow>
      q213603_sum3_vector
        (\<lambda>i. smul (w i) (vsub (points i) (points Q0))) = 0
      \<longrightarrow> (\<forall>i. w i = 0))"

definition q213603_line ::
    "('k::field \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v) \<Rightarrow>
      ('v \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow>
      ('p \<Rightarrow> 'p \<Rightarrow> 'v) \<Rightarrow>
      'p \<Rightarrow> 'p \<Rightarrow> 'p set" where
  "q213603_line smul vadd vsub a b =
    {x. \<exists>r. x = vadd (smul r (vsub b a)) a}"

theorem q213603_cevas_theorem:
  fixes knorm :: "'k::field \<Rightarrow> real"
    and vnorm :: "'v::ab_group_add \<Rightarrow> real"
    and smul :: "'k \<Rightarrow> 'v \<Rightarrow> 'v"
    and vadd :: "'v \<Rightarrow> 'p::metric_space \<Rightarrow> 'p"
    and vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
    and points :: "q213603_fin3 \<Rightarrow> 'p"
    and side_point :: "q213603_fin3 \<Rightarrow> 'p"
    and concurrent_point :: 'p
  assumes normed_field: "q213603_normed_field knorm"
    and seminormed_group: "q213603_seminormed_add_comm_group vnorm"
    and normed_space: "q213603_normed_space knorm vnorm smul"
    and normed_torsor: "q213603_normed_add_torsor vnorm vadd vsub"
    and triangle:
      "q213603_affine_independent_triangle smul vsub points"
    and denominators_nonzero:
      "\<forall>i. side_point i \<noteq> points (q213603_succ2 i)"
    and side_membership:
      "\<forall>i. side_point i \<in>
        q213603_line smul vadd vsub
          (points (q213603_succ i)) (points (q213603_succ2 i))"
    and concurrence:
      "\<forall>i. concurrent_point \<in>
        q213603_line smul vadd vsub (points i) (side_point i)"
  shows
    "q213603_prod3
      (\<lambda>i.
        dist (points (q213603_succ i)) (side_point i) /
        dist (side_point i) (points (q213603_succ2 i))) = 1"
  sorry

end
