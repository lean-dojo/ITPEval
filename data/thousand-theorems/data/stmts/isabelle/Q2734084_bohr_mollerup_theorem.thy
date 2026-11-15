(*
  Statement-only formalization of the thousand-theorems corpus artifact Q2734084,
  "Bohr–Mollerup theorem": every positive real-valued log-convex function on the
  positive reals satisfying the Gamma recurrence and normalized to one at one
  agrees with the real Gamma function on the positive reals. This file contains
  no proof.
*)

theory Q2734084_bohr_mollerup_theorem
  imports "HOL-Analysis.Gamma_Function"
begin

theorem bohr_mollerup_theorem:
  fixes f :: "real \<Rightarrow> real"
  assumes log_convex: "convex_on {0<..} (ln \<circ> f)"
    and recurrence: "\<And>y. 0 < y \<Longrightarrow> f (y + 1) = y * f y"
    and positive: "\<And>y. 0 < y \<Longrightarrow> 0 < f y"
    and normalized: "f 1 = 1"
  shows "\<forall>x \<in> {0<..}. f x = Gamma x"
  sorry

end
