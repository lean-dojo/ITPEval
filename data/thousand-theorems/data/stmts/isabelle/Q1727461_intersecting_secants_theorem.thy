(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1727461 (thousand-theorems__isabelle__Q1727461), "Intersecting secants
  theorem": four cospherical points on two nondegenerate zero-angle secants
  through a point have equal products of distances to that point. This file
  contains no proof.
*)

theory Q1727461_intersecting_secants_theorem
  imports Complex_Main
begin

class q1727461_real_inner = real_normed_vector +
  fixes q1727461_inner :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes q1727461_inner_commute:
      "q1727461_inner x y = q1727461_inner y x"
    and q1727461_inner_add_left:
      "q1727461_inner (x + y) z =
        q1727461_inner x z + q1727461_inner y z"
    and q1727461_inner_scaleR_left:
      "q1727461_inner (scaleR r x) y = r * q1727461_inner x y"
    and q1727461_inner_ge_zero:
      "0 \<le> q1727461_inner x x"
    and q1727461_inner_eq_zero_iff:
      "q1727461_inner x x = 0 \<longleftrightarrow> x = 0"
    and q1727461_norm_eq_sqrt_inner:
      "norm x = sqrt (q1727461_inner x x)"

locale q1727461_euclidean_affine_space =
  fixes q1727461_vadd :: "'v::q1727461_real_inner \<Rightarrow> 'p \<Rightarrow> 'p"
    and q1727461_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q1727461_zero_vadd:
      "q1727461_vadd 0 p = p"
    and q1727461_add_vadd:
      "q1727461_vadd (u + v) p =
        q1727461_vadd u (q1727461_vadd v p)"
    and q1727461_vadd_vsub:
      "q1727461_vadd (q1727461_vsub p q) q = p"
    and q1727461_vsub_vadd:
      "q1727461_vsub (q1727461_vadd v p) p = v"
begin

definition q1727461_dist :: "'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q1727461_dist p q = norm (q1727461_vsub p q)"

definition q1727461_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q1727461_angle a p b =
    arccos (q1727461_inner (q1727461_vsub a p) (q1727461_vsub b p) /
      (norm (q1727461_vsub a p) * norm (q1727461_vsub b p)))"

definition q1727461_cospherical :: "'p set \<Rightarrow> bool" where
  "q1727461_cospherical S \<longleftrightarrow>
    (\<exists>center radius.
      \<forall>x \<in> S. q1727461_dist x center = radius)"

theorem intersecting_secants_theorem:
  fixes a b c d p :: 'p
  assumes cospherical:
      "q1727461_cospherical {a, b, c, d}"
    and first_endpoints_distinct:
      "a \<noteq> b"
    and second_endpoints_distinct:
      "c \<noteq> d"
    and first_angle_zero:
      "q1727461_angle a p b = 0"
    and second_angle_zero:
      "q1727461_angle c p d = 0"
  shows
      "q1727461_dist a p * q1727461_dist b p =
        q1727461_dist c p * q1727461_dist d p"
  sorry

end

end
