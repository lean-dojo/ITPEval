(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q1660147 (thousand-theorems__isabelle__Q1660147), "Mazur–Ulam theorem":
  every bijective isometry between normed real affine spaces is induced by an
  affine isometric equivalence. This file contains no proof.
*)

theory Q1660147_mazur_ulam_theorem
  imports Complex_Main
begin

definition q1660147_normed_add_torsor ::
    "('v::real_normed_vector \<Rightarrow> 'p::metric_space \<Rightarrow> 'p) \<Rightarrow>
      ('p \<Rightarrow> 'p \<Rightarrow> 'v) \<Rightarrow> bool" where
  "q1660147_normed_add_torsor vadd vsub \<longleftrightarrow>
    (\<forall>p. vadd 0 p = p) \<and>
    (\<forall>v w p. vadd (v + w) p = vadd v (vadd w p)) \<and>
    (\<forall>p q. vadd (vsub p q) q = p) \<and>
    (\<forall>v p. vsub (vadd v p) p = v) \<and>
    (\<forall>p q. dist p q = norm (vsub p q))"

theorem q1660147_mazur_ulam:
  fixes vaddE ::
      "'e::real_normed_vector \<Rightarrow> 'pe::metric_space \<Rightarrow> 'pe"
    and vsubE :: "'pe \<Rightarrow> 'pe \<Rightarrow> 'e"
    and vaddF ::
      "'f::real_normed_vector \<Rightarrow> 'pf::metric_space \<Rightarrow> 'pf"
    and vsubF :: "'pf \<Rightarrow> 'pf \<Rightarrow> 'f"
    and g :: "'pe \<Rightarrow> 'pf"
  assumes source_torsor: "q1660147_normed_add_torsor vaddE vsubE"
    and target_torsor: "q1660147_normed_add_torsor vaddF vsubF"
    and isometry: "\<forall>p q. dist (g p) (g q) = dist p q"
    and bijective: "bij g"
  shows
    "\<exists>L :: 'e \<Rightarrow> 'f.
      linear L \<and>
      bij L \<and>
      (\<forall>v. norm (L v) = norm v) \<and>
      (\<forall>v p. g (vaddE v p) = vaddF (L v) (g p))"
  sorry

end
