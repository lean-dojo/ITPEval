(* Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Ptolemy's Theorem\<close>

theory Ptolemys_Theorem
imports
  "HOL-Analysis.Multivariate_Analysis"
begin

subsection \<open>Preliminaries\<close>

subsubsection \<open>Additions to Rat theory\<close>

hide_const (open) normalize

subsubsection \<open>Additions to Transcendental theory\<close>

text \<open>
Lemmas about @{const arcsin} and @{const arccos} commonly involve to show that their argument is
in the domain of those partial functions, i.e., the argument @{term y} is between @{term "-1::real"}
and @{term "1::real"}.
As the argumentation for @{term "(-1::real) \<le> y"} and @{term "y \<le> (1::real)"} is often very similar,
we prefer to prove @{term "\<bar>y\<bar> \<le> (1::real)"} to the two goals above.

The lemma for rewriting the term @{term "cos (arccos y)"} is already provided in the Isabelle
distribution with name @{thm [source] cos_arccos_abs}. Here, we further provide the analogue on
@{term "arcsin"} for rewriting @{term "sin (arcsin y)"}.
\<close>

lemma sin_arcsin_abs: "\<bar>y\<bar> \<le> 1 \<Longrightarrow> sin (arcsin y) = y"
  by sorry

text \<open>
The further lemmas are the required variants from existing lemmas @{thm [source] arccos_lbound}
and @{thm [source] arccos_ubound}.
\<close>

lemma arccos_lbound_abs [simp]:
  "\<bar>y\<bar> \<le> 1 \<Longrightarrow> 0 \<le> arccos y"
  by sorry

lemma arccos_ubound_abs [simp]:
  "\<bar>y\<bar> \<le> 1 \<Longrightarrow> arccos y \<le> pi"
  by sorry

text \<open>
As we choose angles to be between @{term "0::real"} between @{term "2 * pi"},
we need some lemmas to reason about the sign of @{term "sin x"}
for angles @{term "x"}.
\<close>

lemma sin_ge_zero_iff:
  assumes "0 \<le> x" "x < 2 * pi"
  shows "0 \<le> sin x \<longleftrightarrow> x \<le> pi"
  by sorry

lemma sin_less_zero_iff:
  assumes "0 \<le> x" "x < 2 * pi"
  shows "sin x < 0 \<longleftrightarrow> pi < x"
  by sorry

subsubsection \<open>Addition to Finite-Cartesian-Product theory\<close>

text \<open>
Here follow generally useful additions and specialised equations
for two-dimensional real-valued vectors.
\<close>

lemma axis_nth_eq_0 [simp]:
  assumes "i \<noteq> j"
  shows "axis i x $ j = 0"
  by sorry

lemma norm_axis:
  fixes x :: real
  shows "norm (axis i x) = abs x"
  by sorry

lemma norm_eq_on_real_2_vec:
  fixes x :: "real ^ 2"
  shows "norm x = sqrt ((x $ 1) ^ 2 + (x $ 2) ^ 2)"
  by sorry

lemma dist_eq_on_real_2_vec:
  fixes a b :: "real ^ 2"
  shows "dist a b = sqrt ((a $ 1 - b $ 1) ^ 2 + (a $ 2 - b $ 2) ^ 2)"
  by sorry

subsection \<open>Polar Form of Two-Dimensional Real-Valued Vectors\<close>

subsubsection \<open>Definitions to Transfer to Polar Form and Back\<close>

definition of_radiant :: "real \<Rightarrow> real ^ 2"
where
  "of_radiant \<omega> = axis 1 (cos \<omega>) + axis 2 (sin \<omega>)"

definition normalize :: "real ^ 2 \<Rightarrow> real ^ 2"
where
  "normalize p = (if p = 0 then axis 1 1 else (1 / norm p) *\<^sub>R p)"

definition radiant_of :: "real ^ 2 \<Rightarrow> real"
where
  "radiant_of p = (THE \<omega>. 0 \<le> \<omega> \<and> \<omega> < 2 * pi \<and> of_radiant \<omega> = normalize p)"

text \<open>
The vector @{term "of_radiant \<omega>"} is the vector with length @{term "1::real"} and angle @{term "\<omega>"}
to the first axis.
We normalize vectors to length @{term "1::real"} keeping their orientation with the normalize function.
Conversely, @{term "radiant_of p"} is the angle of vector @{term p} to the first axis, where we
choose @{term "radiant_of"} to return angles between @{term "0::real"} and @{term "2 * pi"},
following the usual high-school convention.
With these definitions, we can express the main result
@{term "norm p *\<^sub>R of_radiant (radiant_of p) = p"}.
Note that the main result holds for any definition of @{term "radiant_of 0"}.
So, we choose to define @{term "normalize 0"} and @{term "radiant_of 0"}, such that
@{term "radiant_of 0 = 0"}.
\<close>

subsubsection \<open>Lemmas on @{const of_radiant}\<close>

lemma nth_of_radiant_1 [simp]:
  "of_radiant \<omega> $ 1 = cos \<omega>"
  by sorry

lemma nth_of_radiant_2 [simp]:
  "of_radiant \<omega> $ 2 = sin \<omega>"
  by sorry

lemma norm_of_radiant:
  "norm (of_radiant \<omega>) = 1"
  by sorry

lemma of_radiant_plus_2pi:
  "of_radiant (\<omega> + 2 * pi) = of_radiant \<omega>"
  by sorry

lemma of_radiant_minus_2pi:
  "of_radiant (\<omega> - 2 * pi) = of_radiant \<omega>"
  by sorry

subsubsection \<open>Lemmas on @{const normalize}\<close>

lemma normalize_eq:
  "norm p *\<^sub>R normalize p = p"
  by sorry

lemma norm_normalize:
  "norm (normalize p) = 1"
  by sorry

lemma nth_normalize [simp]:
  "\<bar>normalize p $ i\<bar> \<le> 1"
  by sorry

lemma normalize_square:
  "(normalize p $ 1)\<^sup>2 + (normalize p $ 2)\<^sup>2 = 1"
  by sorry

lemma nth_normalize_ge_zero_iff:
  "0 \<le> normalize p $ i \<longleftrightarrow> 0 \<le> p $ i"
  by sorry

lemma nth_normalize_less_zero_iff:
  "normalize p $ i < 0 \<longleftrightarrow> p $ i < 0"
  by sorry

lemma normalize_boundary_iff:
  "\<bar>normalize p $ 1\<bar> = 1 \<longleftrightarrow> p $ 2 = 0"
  by sorry

lemma between_normalize_if_distant_from_0:
  assumes "norm p \<ge> 1"
  shows "between (0, p) (normalize p)"
  by sorry

lemma between_normalize_if_near_0:
  assumes "norm p \<le> 1"
  shows "between (0, normalize p) p"
  by sorry

subsubsection \<open>Lemmas on @{const radiant_of}\<close>

lemma radiant_of:
  "0 \<le> radiant_of p \<and> radiant_of p < 2 * pi \<and> of_radiant (radiant_of p) = normalize p"
  by sorry

lemma radiant_of_bounds [simp]:
  "0 \<le> radiant_of p" "radiant_of p < 2 * pi"
  by sorry

lemma radiant_of_weak_ubound [simp]:
  "radiant_of p \<le> 2 * pi"
  by sorry

subsubsection \<open>Main Equations for Transforming to Polar Form\<close>

lemma polar_form_eq:
  "norm p *\<^sub>R of_radiant (radiant_of p) = p"
  by sorry

lemma relative_polar_form_eq:
  "Q + dist P Q *\<^sub>R of_radiant (radiant_of (P - Q)) = P"
  by sorry

subsection \<open>Ptolemy's Theorem\<close>

lemma dist_circle_segment:
  assumes "0 \<le> radius" "0 \<le> \<alpha>" "\<alpha> \<le> \<beta>" "\<beta> \<le> 2 * pi"
  shows "dist (center + radius *\<^sub>R of_radiant \<alpha>) (center + radius *\<^sub>R of_radiant \<beta>) = 2 * radius * sin ((\<beta> - \<alpha>) / 2)"
    (is "?lhs = ?rhs")
  by sorry

theorem ptolemy_trigonometric:
  fixes \<omega>\<^sub>1 \<omega>\<^sub>2 \<omega>\<^sub>3 :: real
  shows "sin (\<omega>\<^sub>1 + \<omega>\<^sub>2) * sin (\<omega>\<^sub>2 + \<omega>\<^sub>3) = sin \<omega>\<^sub>1 * sin \<omega>\<^sub>3 + sin \<omega>\<^sub>2 * sin (\<omega>\<^sub>1 + \<omega>\<^sub>2 + \<omega>\<^sub>3)"
  by sorry

theorem ptolemy:
  fixes A B C D center :: "real ^ 2"
  assumes "dist center A = radius" and "dist center B = radius"
  assumes "dist center C = radius" and "dist center D = radius"
  assumes ordering_of_points:
    "radiant_of (A - center) \<le> radiant_of (B - center)"
    "radiant_of (B - center) \<le> radiant_of (C - center)"
    "radiant_of (C - center) \<le> radiant_of (D - center)"
  shows "dist A C * dist B D = dist A B * dist C D + dist A D * dist B C"
  by sorry

end
