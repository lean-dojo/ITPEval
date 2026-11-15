(*
  Statement-only formalization of the thousand-theorems corpus artifact Q530152,
  "Picard&ndash;Lindelöf theorem": local existence for a time-dependent
  Lipschitz vector field on a real Banach space, with an initial point in a
  closed ball and a derivative constrained to a closed time interval. This
  file contains no proof.
*)

theory Q530152_picard_ndash_lindel_f_theorem
  imports "HOL-Analysis.Lipschitz" "HOL-Analysis.Derivative"
begin

definition q530152_is_picard_lindelof ::
    "(real \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
      real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'e \<Rightarrow>
      real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "q530152_is_picard_lindelof f tmin tmax t0 x0 a r L K \<longleftrightarrow>
    0 \<le> a \<and> 0 \<le> r \<and> 0 \<le> L \<and> 0 \<le> K \<and>
    t0 \<in> {tmin..tmax} \<and>
    (\<forall>t \<in> {tmin..tmax}. K-lipschitz_on (cball x0 a) (f t)) \<and>
    (\<forall>y \<in> cball x0 a. continuous_on {tmin..tmax} (\<lambda>t. f t y)) \<and>
    (\<forall>t \<in> {tmin..tmax}. \<forall>y \<in> cball x0 a. norm (f t y) \<le> L) \<and>
    L * max (tmax - t0) (t0 - tmin) \<le> a - r"

theorem picard_lindelof:
  fixes f :: "real \<Rightarrow> 'e::banach \<Rightarrow> 'e"
    and tmin tmax t0 :: real
    and x0 x :: 'e
    and a r L K :: real
  assumes picard_lindelof_conditions:
      "q530152_is_picard_lindelof f tmin tmax t0 x0 a r L K"
    and initial_point: "x \<in> cball x0 r"
  shows "\<exists>\<alpha> :: real \<Rightarrow> 'e.
    \<alpha> t0 = x \<and>
    (\<forall>t \<in> {tmin..tmax}.
      (\<alpha> has_vector_derivative (f t (\<alpha> t)))
        (at t within {tmin..tmax}))"
  sorry

end
