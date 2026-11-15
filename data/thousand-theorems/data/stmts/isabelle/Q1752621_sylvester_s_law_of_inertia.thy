(*
  Statement-only formalization of thousand-theorems corpus artifact Q1752621,
  "Sylvester's law of inertia": every quadratic form on a finite-dimensional
  real vector space is equivalent to a diagonal weighted sum of squares whose
  weights are -1, 0, or 1. This file contains no proof.
*)

theory Q1752621_sylvester_s_law_of_inertia
  imports Complex_Main
begin

definition q1752621_bilinear ::
    "('e::real_vector \<Rightarrow> 'e \<Rightarrow> real) \<Rightarrow> bool" where
  "q1752621_bilinear B \<longleftrightarrow>
    (\<forall>x y z. B (x + y) z = B x z + B y z) \<and>
    (\<forall>a x y. B (a *\<^sub>R x) y = a * B x y) \<and>
    (\<forall>x y z. B x (y + z) = B x y + B x z) \<and>
    (\<forall>a x y. B x (a *\<^sub>R y) = a * B x y)"

definition q1752621_quadratic_form ::
    "('e::real_vector \<Rightarrow> real) \<Rightarrow> bool" where
  "q1752621_quadratic_form Q \<longleftrightarrow>
    (\<exists>B :: 'e \<Rightarrow> 'e \<Rightarrow> real.
      q1752621_bilinear B \<and>
      (\<forall>x y. B x y = B y x) \<and>
      (\<forall>x. Q x = B x x))"

definition q1752621_linear_combination ::
    "('e::real_vector \<Rightarrow> real) \<Rightarrow> 'e set \<Rightarrow> 'e" where
  "q1752621_linear_combination c S =
    (\<Sum>b\<in>S. c b *\<^sub>R b)"

definition q1752621_basis ::
    "'e::real_vector set \<Rightarrow> bool" where
  "q1752621_basis S \<longleftrightarrow>
    finite S \<and>
    (\<forall>c :: 'e \<Rightarrow> real.
      q1752621_linear_combination c S = 0 \<longrightarrow>
      (\<forall>b\<in>S. c b = 0)) \<and>
    (\<forall>x. \<exists>c :: 'e \<Rightarrow> real.
      q1752621_linear_combination c S = x)"

definition q1752621_finite_dimensional ::
    "'e::real_vector itself \<Rightarrow> bool" where
  "q1752621_finite_dimensional _ \<longleftrightarrow>
    (\<exists>S :: 'e set. q1752621_basis S)"

theorem sylvester_s_law_of_inertia:
  fixes Q :: "'e::real_vector \<Rightarrow> real"
  assumes finite_dimensional:
      "q1752621_finite_dimensional TYPE('e)"
    and quadratic_form:
      "q1752621_quadratic_form Q"
  shows "\<exists>S w coord.
    q1752621_basis S \<and>
    (\<forall>b\<in>S. w b = -1 \<or> w b = 0 \<or> w b = 1) \<and>
    (\<forall>x.
      q1752621_linear_combination (coord x) S = x \<and>
      Q x = (\<Sum>b\<in>S. w b * (coord x b)\<^sup>2))"
  sorry

end
