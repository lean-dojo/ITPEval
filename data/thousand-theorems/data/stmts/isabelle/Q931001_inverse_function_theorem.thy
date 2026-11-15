(*
  Statement-only formalization of thousand-theorems corpus artifact Q931001,
  "Inverse function theorem": a map between normed spaces over an arbitrary
  nontrivially normed field, with complete domain and an invertible strict
  Frechet derivative at a point, has a choice-constructed local inverse whose
  strict derivative is the inverse linear equivalence. This file contains no
  proof.
*)

theory Q931001_inverse_function_theorem
  imports Complex_Main
begin

definition q931001_nontrivially_normed_field ::
    "('k::field \<Rightarrow> real) \<Rightarrow> bool" where
  "q931001_nontrivially_normed_field knorm \<longleftrightarrow>
    knorm 0 = 0 \<and>
    (\<forall>a. 0 \<le> knorm a) \<and>
    (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
    (\<forall>a. knorm (-a) = knorm a) \<and>
    (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
    (\<forall>a b. knorm (a * b) = knorm a * knorm b) \<and>
    (\<exists>a. 1 < knorm a)"

definition q931001_normed_space ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
      ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q931001_normed_space knorm enorm scale \<longleftrightarrow>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>a x. enorm (scale a x) = knorm a * enorm x) \<and>
    enorm 0 = 0 \<and>
    (\<forall>x. 0 \<le> enorm x) \<and>
    (\<forall>x. enorm x = 0 \<longleftrightarrow> x = 0) \<and>
    (\<forall>x. enorm (-x) = enorm x) \<and>
    (\<forall>x y. enorm (x + y) \<le> enorm x + enorm y)"

definition q931001_complete_space ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> bool" where
  "q931001_complete_space enorm \<longleftrightarrow>
    (\<forall>u :: nat \<Rightarrow> 'e.
      (\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
        enorm (u m - u n) < epsilon)
      \<longrightarrow>
      (\<exists>x. \<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        enorm (u n - x) < epsilon))"

definition q931001_continuous_linear ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k::field \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
      ('k \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> bool" where
  "q931001_continuous_linear enorm fnorm escale fscale L \<longleftrightarrow>
    (\<forall>x y. L (x + y) = L x + L y) \<and>
    (\<forall>a x. L (escale a x) = fscale a (L x)) \<and>
    (\<exists>C\<ge>0. \<forall>x. fnorm (L x) \<le> C * enorm x)"

definition q931001_continuous_linear_equiv ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k::field \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
      ('k \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q931001_continuous_linear_equiv enorm fnorm escale fscale D Dinv
      \<longleftrightarrow>
    q931001_continuous_linear enorm fnorm escale fscale D \<and>
    q931001_continuous_linear fnorm enorm fscale escale Dinv \<and>
    (\<forall>x. Dinv (D x) = x) \<and>
    (\<forall>y. D (Dinv y) = y)"

definition q931001_has_strict_fderiv_at ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k::field \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
      ('k \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow>
      'e \<Rightarrow> bool" where
  "q931001_has_strict_fderiv_at enorm fnorm escale fscale f D a
      \<longleftrightarrow>
    q931001_continuous_linear enorm fnorm escale fscale D \<and>
    (\<forall>epsilon>0. \<exists>delta>0. \<forall>x y.
      enorm (x - a) < delta \<longrightarrow>
      enorm (y - a) < delta \<longrightarrow>
      fnorm ((f x - f y) - D (x - y))
        \<le> epsilon * enorm (x - y))"

definition q931001_open_norm ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q931001_open_norm enorm U \<longleftrightarrow>
    (\<forall>x\<in>U. \<exists>r>0. \<forall>y.
      enorm (y - x) < r \<longrightarrow> y \<in> U)"

definition q931001_continuous_on_norm ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      'e set \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> bool" where
  "q931001_continuous_on_norm enorm fnorm U h \<longleftrightarrow>
    (\<forall>x\<in>U. \<forall>epsilon>0. \<exists>delta>0. \<forall>y\<in>U.
      enorm (y - x) < delta \<longrightarrow>
      fnorm (h y - h x) < epsilon)"

definition q931001_open_partial_homeomorphism ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> 'e \<Rightarrow>
      ('e set \<times> ('f set \<times> ('f \<Rightarrow> 'e))) \<Rightarrow> bool" where
  "q931001_open_partial_homeomorphism enorm fnorm f a chart \<longleftrightarrow>
    (let source = fst chart;
         target = fst (snd chart);
         inverse = snd (snd chart)
     in q931001_open_norm enorm source \<and>
        q931001_open_norm fnorm target \<and>
        a \<in> source \<and>
        f a \<in> target \<and>
        q931001_continuous_on_norm enorm fnorm source f \<and>
        q931001_continuous_on_norm fnorm enorm target inverse \<and>
        (\<forall>x\<in>source. f x \<in> target \<and> inverse (f x) = x) \<and>
        (\<forall>y\<in>target. inverse y \<in> source \<and> f (inverse y) = y))"

definition q931001_to_open_partial_homeomorphism ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
      ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
      ('k \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow>
      ('f \<Rightarrow> 'e) \<Rightarrow> 'e \<Rightarrow>
      ('e set \<times> ('f set \<times> ('f \<Rightarrow> 'e)))" where
  "q931001_to_open_partial_homeomorphism
      knorm enorm fnorm escale fscale f D Dinv a =
    (SOME chart.
      q931001_nontrivially_normed_field knorm \<and>
      q931001_normed_space knorm enorm escale \<and>
      q931001_normed_space knorm fnorm fscale \<and>
      q931001_complete_space enorm \<and>
      q931001_continuous_linear_equiv
        enorm fnorm escale fscale D Dinv \<and>
      q931001_has_strict_fderiv_at
        enorm fnorm escale fscale f D a \<and>
      q931001_open_partial_homeomorphism enorm fnorm f a chart)"

definition q931001_local_inverse ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
      ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
      ('k \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow>
      ('f \<Rightarrow> 'e) \<Rightarrow> 'e \<Rightarrow> ('f \<Rightarrow> 'e)" where
  "q931001_local_inverse knorm enorm fnorm escale fscale f D Dinv a =
    snd (snd (q931001_to_open_partial_homeomorphism
      knorm enorm fnorm escale fscale f D Dinv a))"

theorem q931001_inverse_function_theorem:
  fixes knorm :: "'k::field \<Rightarrow> real"
    and enorm :: "'e::ab_group_add \<Rightarrow> real"
    and fnorm :: "'f::ab_group_add \<Rightarrow> real"
    and escale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and fscale :: "'k \<Rightarrow> 'f \<Rightarrow> 'f"
    and f :: "'e \<Rightarrow> 'f"
    and D :: "'e \<Rightarrow> 'f"
    and Dinv :: "'f \<Rightarrow> 'e"
    and a :: 'e
  assumes scalar_field: "q931001_nontrivially_normed_field knorm"
    and domain_space: "q931001_normed_space knorm enorm escale"
    and codomain_space: "q931001_normed_space knorm fnorm fscale"
    and domain_complete: "q931001_complete_space enorm"
    and derivative_equiv:
      "q931001_continuous_linear_equiv
        enorm fnorm escale fscale D Dinv"
    and strict_derivative:
      "q931001_has_strict_fderiv_at
        enorm fnorm escale fscale f D a"
  shows "q931001_has_strict_fderiv_at
    fnorm enorm fscale escale
    (q931001_local_inverse
      knorm enorm fnorm escale fscale f D Dinv a)
    Dinv (f a)"
  sorry

end
