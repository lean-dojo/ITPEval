(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q1472120 (thousand-theorems__isabelle__Q1472120),
  "Hellinger&ndash;Toeplitz theorem": every everywhere-defined symmetric
  linear endomorphism of a complete real or complex inner-product space is
  continuous. This file contains no proof.
*)

theory Q1472120_hellinger_ndash_toeplitz_theorem
  imports "HOL-Analysis.Inner_Product"
begin

definition q1472120_complex_vector_space ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1472120_complex_vector_space cscale \<longleftrightarrow>
    (\<forall>a x y. cscale a (x + y) = cscale a x + cscale a y) \<and>
    (\<forall>a b x. cscale (a + b) x = cscale a x + cscale b x) \<and>
    (\<forall>a b x. cscale (a * b) x = cscale a (cscale b x)) \<and>
    (\<forall>x. cscale 1 x = x) \<and>
    (\<forall>r x. cscale (of_real r) x = scaleR r x) \<and>
    (\<forall>a x. norm (cscale a x) = norm a * norm x)"

definition q1472120_complex_inner_product_space ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
     ('e \<Rightarrow> 'e \<Rightarrow> complex) \<Rightarrow> bool" where
  "q1472120_complex_inner_product_space cscale cinner \<longleftrightarrow>
    q1472120_complex_vector_space cscale \<and>
    (\<forall>x y z. cinner (x + y) z = cinner x z + cinner y z) \<and>
    (\<forall>a x y. cinner (cscale a x) y = cnj a * cinner x y) \<and>
    (\<forall>x y z. cinner x (y + z) = cinner x y + cinner x z) \<and>
    (\<forall>a x y. cinner x (cscale a y) = a * cinner x y) \<and>
    (\<forall>x y. cinner x y = cnj (cinner y x)) \<and>
    (\<forall>x. cinner x x = of_real (norm x ^ 2))"

definition q1472120_complex_linear ::
    "(complex \<Rightarrow> 'e::real_normed_vector \<Rightarrow> 'e) \<Rightarrow>
     ('e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1472120_complex_linear cscale T \<longleftrightarrow>
    (\<forall>x y. T (x + y) = T x + T y) \<and>
    (\<forall>a x. T (cscale a x) = cscale a (T x))"

definition q1472120_complex_symmetric ::
    "('e \<Rightarrow> 'e \<Rightarrow> complex) \<Rightarrow>
     ('e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q1472120_complex_symmetric cinner T \<longleftrightarrow>
    (\<forall>x y. cinner (T x) y = cinner x (T y))"

theorem hellinger_toeplitz_real:
  fixes T :: "'e::{real_inner,complete_space} \<Rightarrow> 'e"
  assumes linear: "linear T"
    and symmetric: "\<forall>x y. inner (T x) y = inner x (T y)"
  shows "continuous_on UNIV T"
  sorry

theorem hellinger_toeplitz_complex:
  fixes cscale ::
      "complex \<Rightarrow> 'e::{real_normed_vector,complete_space} \<Rightarrow> 'e"
    and cinner :: "'e \<Rightarrow> 'e \<Rightarrow> complex"
    and T :: "'e \<Rightarrow> 'e"
  assumes hilbert_space: "q1472120_complex_inner_product_space cscale cinner"
    and linear: "q1472120_complex_linear cscale T"
    and symmetric: "q1472120_complex_symmetric cinner T"
  shows "continuous_on UNIV T"
  sorry

end
