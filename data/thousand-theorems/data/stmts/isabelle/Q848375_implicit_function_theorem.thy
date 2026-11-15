(*
  Statement-only formalization of thousand-theorems corpus artifact Q848375,
  "Implicit function theorem": for general implicit-function data on Banach
  spaces over an arbitrary nontrivially normed field, the implicit function is
  the curried inverse of the associated local product-map homeomorphism. This
  file contains no proof.
*)

theory Q848375_implicit_function_theorem
  imports Complex_Main
begin

definition q848375_nontrivially_normed_field ::
    "('k::field \<Rightarrow> real) \<Rightarrow> bool" where
  "q848375_nontrivially_normed_field knorm \<longleftrightarrow>
    knorm 0 = 0 \<and>
    (\<forall>a. 0 \<le> knorm a) \<and>
    (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
    (\<forall>a. knorm (-a) = knorm a) \<and>
    (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
    (\<forall>a b. knorm (a * b) = knorm a * knorm b) \<and>
    (\<exists>a. 1 < knorm a)"

definition q848375_normed_space ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
      ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q848375_normed_space knorm enorm scale \<longleftrightarrow>
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

definition q848375_complete_space ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> bool" where
  "q848375_complete_space enorm \<longleftrightarrow>
    (\<forall>u :: nat \<Rightarrow> 'e.
      (\<forall>epsilon>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.
        enorm (u m - u n) < epsilon)
      \<longrightarrow>
      (\<exists>x. \<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
        enorm (u n - x) < epsilon))"

definition q848375_continuous_linear ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k::field \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
      ('k \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> bool" where
  "q848375_continuous_linear enorm fnorm escale fscale L \<longleftrightarrow>
    (\<forall>x y. L (x + y) = L x + L y) \<and>
    (\<forall>a x. L (escale a x) = fscale a (L x)) \<and>
    (\<exists>C\<ge>0. \<forall>x. fnorm (L x) \<le> C * enorm x)"

definition q848375_has_strict_fderiv_at ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k::field \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
      ('k \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> 'e \<Rightarrow> bool" where
  "q848375_has_strict_fderiv_at enorm fnorm escale fscale f D a \<longleftrightarrow>
    q848375_continuous_linear enorm fnorm escale fscale D \<and>
    (\<forall>epsilon>0. \<exists>delta>0. \<forall>x y.
      enorm (x - a) < delta \<longrightarrow>
      enorm (y - a) < delta \<longrightarrow>
      fnorm ((f x - f y) - D (x - y)) \<le> epsilon * enorm (x - y))"

definition q848375_complementary_kernels ::
    "('e::ab_group_add \<Rightarrow> 'f::zero) \<Rightarrow>
      ('e \<Rightarrow> 'g::zero) \<Rightarrow> bool" where
  "q848375_complementary_kernels L R \<longleftrightarrow>
    (\<forall>x. \<exists>u v. L u = 0 \<and> R v = 0 \<and> x = u + v) \<and>
    (\<forall>x. L x = 0 \<longrightarrow> R x = 0 \<longrightarrow> x = 0)"

definition q848375_open_norm ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q848375_open_norm enorm U \<longleftrightarrow>
    (\<forall>x\<in>U. \<exists>r>0. \<forall>y. enorm (y - x) < r \<longrightarrow> y \<in> U)"

definition q848375_open_product_norm ::
    "('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('g::ab_group_add \<Rightarrow> real) \<Rightarrow> ('f \<times> 'g) set \<Rightarrow> bool" where
  "q848375_open_product_norm fnorm gnorm U \<longleftrightarrow>
    (\<forall>p\<in>U. \<exists>r>0. \<forall>q.
      fnorm (fst q - fst p) < r \<longrightarrow>
      gnorm (snd q - snd p) < r \<longrightarrow>
      q \<in> U)"

definition q848375_forward_continuous_on ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('g::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('e \<Rightarrow> 'f) \<Rightarrow> ('e \<Rightarrow> 'g) \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q848375_forward_continuous_on enorm fnorm gnorm f g U \<longleftrightarrow>
    (\<forall>x\<in>U. \<forall>epsilon>0. \<exists>delta>0. \<forall>y\<in>U.
      enorm (y - x) < delta \<longrightarrow>
      fnorm (f y - f x) < epsilon \<and>
      gnorm (g y - g x) < epsilon)"

definition q848375_inverse_continuous_on ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('g::ab_group_add \<Rightarrow> real) \<Rightarrow>
      (('f \<times> 'g) \<Rightarrow> 'e) \<Rightarrow> ('f \<times> 'g) set \<Rightarrow> bool" where
  "q848375_inverse_continuous_on enorm fnorm gnorm h U \<longleftrightarrow>
    (\<forall>p\<in>U. \<forall>epsilon>0. \<exists>delta>0. \<forall>q\<in>U.
      fnorm (fst q - fst p) < delta \<longrightarrow>
      gnorm (snd q - snd p) < delta \<longrightarrow>
      enorm (h q - h p) < epsilon)"

locale q848375_implicit_function_data =
  fixes knorm :: "'k::field \<Rightarrow> real"
    and enorm :: "'e::ab_group_add \<Rightarrow> real"
    and fnorm :: "'f::ab_group_add \<Rightarrow> real"
    and gnorm :: "'g::ab_group_add \<Rightarrow> real"
    and escale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and fscale :: "'k \<Rightarrow> 'f \<Rightarrow> 'f"
    and gscale :: "'k \<Rightarrow> 'g \<Rightarrow> 'g"
    and leftFun :: "'e \<Rightarrow> 'f"
    and leftDeriv :: "'e \<Rightarrow> 'f"
    and rightFun :: "'e \<Rightarrow> 'g"
    and rightDeriv :: "'e \<Rightarrow> 'g"
    and pt :: 'e
  assumes scalar_field: "q848375_nontrivially_normed_field knorm"
    and domain_space: "q848375_normed_space knorm enorm escale"
    and left_space: "q848375_normed_space knorm fnorm fscale"
    and right_space: "q848375_normed_space knorm gnorm gscale"
    and domain_complete: "q848375_complete_space enorm"
    and left_complete: "q848375_complete_space fnorm"
    and right_complete: "q848375_complete_space gnorm"
    and left_strict_derivative:
      "q848375_has_strict_fderiv_at
        enorm fnorm escale fscale leftFun leftDeriv pt"
    and right_strict_derivative:
      "q848375_has_strict_fderiv_at
        enorm gnorm escale gscale rightFun rightDeriv pt"
    and left_surjective: "\<forall>y. \<exists>x. leftDeriv x = y"
    and right_surjective: "\<forall>z. \<exists>x. rightDeriv x = z"
    and complementary:
      "q848375_complementary_kernels leftDeriv rightDeriv"
begin

definition q848375_local_product_homeomorphism ::
    "'e set \<Rightarrow> ('f \<times> 'g) set \<Rightarrow>
      (('f \<times> 'g) \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q848375_local_product_homeomorphism source target invFun \<longleftrightarrow>
    q848375_open_norm enorm source \<and>
    q848375_open_product_norm fnorm gnorm target \<and>
    pt \<in> source \<and>
    (leftFun pt, rightFun pt) \<in> target \<and>
    q848375_forward_continuous_on
      enorm fnorm gnorm leftFun rightFun source \<and>
    q848375_inverse_continuous_on
      enorm fnorm gnorm invFun target \<and>
    (\<forall>x\<in>source.
      (leftFun x, rightFun x) \<in> target \<and>
      invFun (leftFun x, rightFun x) = x) \<and>
    (\<forall>p\<in>target.
      invFun p \<in> source \<and>
      leftFun (invFun p) = fst p \<and>
      rightFun (invFun p) = snd p)"

definition q848375_to_open_partial_homeomorph ::
    "'e set \<times> (('f \<times> 'g) set \<times> (('f \<times> 'g) \<Rightarrow> 'e))" where
  "q848375_to_open_partial_homeomorph =
    (SOME chart.
      q848375_local_product_homeomorphism
        (fst chart) (fst (snd chart)) (snd (snd chart)))"

definition q848375_implicit_function :: "'f \<Rightarrow> 'g \<Rightarrow> 'e" where
  "q848375_implicit_function =
    curry (snd (snd q848375_to_open_partial_homeomorph))"

theorem q848375_to_open_partial_homeomorph_spec:
  "q848375_local_product_homeomorphism
    (fst q848375_to_open_partial_homeomorph)
    (fst (snd q848375_to_open_partial_homeomorph))
    (snd (snd q848375_to_open_partial_homeomorph))"
  sorry

end

end
