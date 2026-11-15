(*
  Statement-only formalization of the thousand-theorems corpus artifact
  thousand-theorems__isabelle__Q660799, "Darboux's theorem (analysis)":
  derivatives of real functions on intervals take every intermediate value,
  and their images are order-connected or convex. This file contains no proof.
*)

theory Q660799_darboux_s_theorem_analysis
  imports "HOL-Analysis.Derivative"
begin

definition q660799_has_deriv_within_at ::
    "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> bool" where
  "q660799_has_deriv_within_at f d S x \<longleftrightarrow>
    (f has_vector_derivative d) (at x within S)"

definition q660799_differentiable_on ::
    "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "q660799_differentiable_on f S \<longleftrightarrow>
    (\<forall>x \<in> S. \<exists>d. q660799_has_deriv_within_at f d S x)"

definition q660799_deriv_within ::
    "(real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real" where
  "q660799_deriv_within f S x =
    (if q660799_has_deriv_within_at f 0 S x then 0
     else if \<exists>d. q660799_has_deriv_within_at f d S x
     then (SOME d. q660799_has_deriv_within_at f d S x)
     else 0)"

definition q660799_ord_connected :: "real set \<Rightarrow> bool" where
  "q660799_ord_connected S \<longleftrightarrow>
    (\<forall>a \<in> S. \<forall>b \<in> S. \<forall>x.
      a \<le> x \<and> x \<le> b \<longrightarrow> x \<in> S)"

theorem exists_hasDerivWithinAt_eq_of_gt_of_lt:
  fixes a b m :: real
    and f f' :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "\<forall>x \<in> {a..b}.
      q660799_has_deriv_within_at f (f' x) {a..b} x"
    and "f' a < m"
    and "m < f' b"
  shows "m \<in> f' ` {a<..<b}"
  sorry

theorem exists_hasDerivWithinAt_eq_of_lt_of_gt:
  fixes a b m :: real
    and f f' :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "\<forall>x \<in> {a..b}.
      q660799_has_deriv_within_at f (f' x) {a..b} x"
    and "m < f' a"
    and "f' b < m"
  shows "m \<in> f' ` {a<..<b}"
  sorry

theorem Set_OrdConnected_image_hasDerivWithinAt:
  fixes S :: "real set"
    and f f' :: "real \<Rightarrow> real"
  assumes "q660799_ord_connected S"
    and "\<forall>x \<in> S. q660799_has_deriv_within_at f (f' x) S x"
  shows "q660799_ord_connected (f' ` S)"
  sorry

theorem Set_OrdConnected_image_derivWithin:
  fixes S :: "real set"
    and f :: "real \<Rightarrow> real"
  assumes "q660799_ord_connected S"
    and "q660799_differentiable_on f S"
  shows "q660799_ord_connected (q660799_deriv_within f S ` S)"
  sorry

theorem Set_OrdConnected_image_deriv:
  fixes S :: "real set"
    and f :: "real \<Rightarrow> real"
  assumes "q660799_ord_connected S"
    and "\<forall>x \<in> S. f differentiable (at x)"
  shows "q660799_ord_connected (deriv f ` S)"
  sorry

theorem Convex_image_hasDerivWithinAt:
  fixes S :: "real set"
    and f f' :: "real \<Rightarrow> real"
  assumes "convex S"
    and "\<forall>x \<in> S. q660799_has_deriv_within_at f (f' x) S x"
  shows "convex (f' ` S)"
  sorry

theorem Convex_image_derivWithin:
  fixes S :: "real set"
    and f :: "real \<Rightarrow> real"
  assumes "convex S"
    and "q660799_differentiable_on f S"
  shows "convex (q660799_deriv_within f S ` S)"
  sorry

theorem Convex_image_deriv:
  fixes S :: "real set"
    and f :: "real \<Rightarrow> real"
  assumes "convex S"
    and "\<forall>x \<in> S. f differentiable (at x)"
  shows "convex (deriv f ` S)"
  sorry

theorem exists_hasDerivWithinAt_eq_of_ge_of_le:
  fixes a b m :: real
    and f f' :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "\<forall>x \<in> {a..b}.
      q660799_has_deriv_within_at f (f' x) {a..b} x"
    and "f' a \<le> m"
    and "m \<le> f' b"
  shows "m \<in> f' ` {a..b}"
  sorry

theorem exists_hasDerivWithinAt_eq_of_le_of_ge:
  fixes a b m :: real
    and f f' :: "real \<Rightarrow> real"
  assumes "a \<le> b"
    and "\<forall>x \<in> {a..b}.
      q660799_has_deriv_within_at f (f' x) {a..b} x"
    and "f' a \<le> m"
    and "m \<le> f' b"
  shows "m \<in> f' ` {a..b}"
  sorry

end
