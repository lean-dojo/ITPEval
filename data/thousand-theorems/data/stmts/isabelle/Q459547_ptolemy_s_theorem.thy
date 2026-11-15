(*
  Statement-only formalization of thousand-theorems corpus artifact Q459547,
  "Ptolemy's theorem": four cospherical points in a real inner-product affine
  space satisfy Ptolemy's distance identity when a point forms straight angles
  across both diagonals. This file contains no proof.
*)

theory Q459547_ptolemy_s_theorem
  imports Complex_Main
begin

class q459547_real_inner = real_normed_vector +
  fixes q459547_inner :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes q459547_inner_commute:
      "q459547_inner x y = q459547_inner y x"
    and q459547_inner_add_left:
      "q459547_inner (x + y) z =
        q459547_inner x z + q459547_inner y z"
    and q459547_inner_scaleR_left:
      "q459547_inner (scaleR r x) y = r * q459547_inner x y"
    and q459547_inner_ge_zero:
      "0 \<le> q459547_inner x x"
    and q459547_inner_eq_zero_iff:
      "q459547_inner x x = 0 \<longleftrightarrow> x = 0"
    and q459547_norm_eq_sqrt_inner:
      "norm x = sqrt (q459547_inner x x)"

locale q459547_euclidean_affine_space =
  fixes q459547_vadd :: "'v::q459547_real_inner \<Rightarrow> 'p \<Rightarrow> 'p"
    and q459547_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q459547_zero_vadd:
      "q459547_vadd 0 p = p"
    and q459547_add_vadd:
      "q459547_vadd (u + v) p =
        q459547_vadd u (q459547_vadd v p)"
    and q459547_vadd_vsub:
      "q459547_vadd (q459547_vsub p q) q = p"
    and q459547_vsub_vadd:
      "q459547_vsub (q459547_vadd v p) p = v"
begin

definition q459547_dist :: "'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q459547_dist p q = norm (q459547_vsub p q)"

definition q459547_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q459547_angle a p c =
    arccos (q459547_inner (q459547_vsub a p) (q459547_vsub c p) /
      (norm (q459547_vsub a p) * norm (q459547_vsub c p)))"

definition q459547_cospherical :: "'p set \<Rightarrow> bool" where
  "q459547_cospherical S \<longleftrightarrow>
    (\<exists>center radius.
      \<forall>x \<in> S. q459547_dist x center = radius)"

theorem ptolemy_s_theorem:
  fixes a b c d p :: 'p
  assumes cospherical:
      "q459547_cospherical {a, b, c, d}"
    and diagonal_ac:
      "q459547_angle a p c = pi"
    and diagonal_bd:
      "q459547_angle b p d = pi"
  shows
      "q459547_dist a b * q459547_dist c d +
        q459547_dist b c * q459547_dist d a =
        q459547_dist a c * q459547_dist b d"
  sorry

end

end
