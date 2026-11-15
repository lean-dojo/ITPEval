(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q1357684 (thousand-theorems__isabelle__Q1357684), "Riesz representation
  theorem": every bounded linear functional on a real or complex Hilbert
  space has a unique inner-product representing vector, with the same
  operator norm. This file contains no proof.
*)

theory Q1357684_riesz_representation_theorem
  imports Complex_Main
begin

definition q1357684_operator_norm ::
    "('e::real_normed_vector \<Rightarrow> 'f::real_normed_vector) \<Rightarrow> real" where
  "q1357684_operator_norm f =
    Sup {norm (f x) | x. norm x \<le> 1}"

definition q1357684_real_inner_product_space ::
    "('e::real_normed_vector \<Rightarrow> 'e \<Rightarrow> real) \<Rightarrow> bool" where
  "q1357684_real_inner_product_space ip \<longleftrightarrow>
    (\<forall>x y z. ip (x + y) z = ip x z + ip y z) \<and>
    (\<forall>r x y. ip (scaleR r x) y = r * ip x y) \<and>
    (\<forall>x y. ip x y = ip y x) \<and>
    (\<forall>x. ip x x = norm x ^ 2)"

definition q1357684_real_linear ::
    "('e::real_normed_vector \<Rightarrow> real) \<Rightarrow> bool" where
  "q1357684_real_linear f \<longleftrightarrow>
    (\<forall>x y. f (x + y) = f x + f y) \<and>
    (\<forall>r x. f (scaleR r x) = r * f x)"

definition q1357684_complex_vector_space ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1357684_complex_vector_space scale \<longleftrightarrow>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>r x. scale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (scale a x) = norm a * norm x)"

definition q1357684_complex_inner_product_space ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
     ('e \<Rightarrow> 'e \<Rightarrow> complex) \<Rightarrow> bool" where
  "q1357684_complex_inner_product_space scale ip \<longleftrightarrow>
    q1357684_complex_vector_space scale \<and>
    (\<forall>x y z. ip x (y + z) = ip x y + ip x z) \<and>
    (\<forall>a x y. ip x (scale a y) = a * ip x y) \<and>
    (\<forall>x y. ip x y = cnj (ip y x)) \<and>
    (\<forall>x. ip x x = of_real (norm x ^ 2))"

definition q1357684_complex_linear ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
     ('e \<Rightarrow> complex) \<Rightarrow> bool" where
  "q1357684_complex_linear scale f \<longleftrightarrow>
    (\<forall>x y. f (x + y) = f x + f y) \<and>
    (\<forall>a x. f (scale a x) = a * f x)"

definition q1357684_bounded ::
    "('e::real_normed_vector \<Rightarrow> 'f::real_normed_vector) \<Rightarrow> bool" where
  "q1357684_bounded f \<longleftrightarrow>
    (\<exists>C \<ge> 0. \<forall>x. norm (f x) \<le> C * norm x)"

theorem riesz_representation_real:
  fixes ip :: "'e::{real_normed_vector,complete_space} \<Rightarrow> 'e \<Rightarrow> real"
    and f :: "'e \<Rightarrow> real"
  assumes "q1357684_real_inner_product_space ip"
    and "q1357684_real_linear f"
    and "q1357684_bounded f"
  shows "\<exists>y.
    (\<forall>x. f x = ip y x) \<and>
    norm y = q1357684_operator_norm f \<and>
    (\<forall>z. (\<forall>x. f x = ip z x) \<longrightarrow> z = y)"
  sorry

theorem riesz_representation_complex:
  fixes scale :: "complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e"
    and ip :: "'e \<Rightarrow> 'e \<Rightarrow> complex"
    and f :: "'e \<Rightarrow> complex"
  assumes "q1357684_complex_inner_product_space scale ip"
    and "q1357684_complex_linear scale f"
    and "q1357684_bounded f"
  shows "\<exists>y.
    (\<forall>x. f x = ip y x) \<and>
    norm y = q1357684_operator_norm f \<and>
    (\<forall>z. (\<forall>x. f x = ip z x) \<longrightarrow> z = y)"
  sorry

end
