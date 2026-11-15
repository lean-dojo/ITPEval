(*
  Statement-only formalization of thousand-theorems corpus artifact Q1306095,
  "Whitney embedding theorem": every compact Hausdorff smooth finite-dimensional
  real manifold admits a smooth closed embedding into some finite-dimensional
  Euclidean space whose manifold derivative is injective everywhere. This file
  contains no proof.
*)

theory Q1306095_whitney_embedding_theorem
  imports "HOL-Analysis.Derivative"
begin

record ('m, 'e, 'c) q1306095_manifold_data =
  q1306095_topology :: "'m topology"
  q1306095_model_carrier :: "'e set"
  q1306095_chart_source :: "'c \<Rightarrow> 'm set"
  q1306095_chart_target :: "'c \<Rightarrow> 'e set"
  q1306095_to_chart :: "'c \<Rightarrow> 'm \<Rightarrow> 'e"
  q1306095_from_chart :: "'c \<Rightarrow> 'e \<Rightarrow> 'm"
  q1306095_chart_at :: "'m \<Rightarrow> 'c"

definition q1306095_multilinear ::
    "nat \<Rightarrow> ('e::real_normed_vector list \<Rightarrow> 'f::real_normed_vector) \<Rightarrow> bool" where
  "q1306095_multilinear k A \<longleftrightarrow>
    (\<forall>xs i u v.
      length xs = k \<longrightarrow> i < k \<longrightarrow>
      A (xs[i := u + v]) = A (xs[i := u]) + A (xs[i := v])) \<and>
    (\<forall>xs i r u.
      length xs = k \<longrightarrow> i < k \<longrightarrow>
      A (xs[i := r *\<^sub>R u]) = r *\<^sub>R A (xs[i := u])) \<and>
    (\<exists>C\<ge>0. \<forall>xs. length xs = k \<longrightarrow>
      norm (A xs) \<le> C * (\<Prod>i<k. norm (xs ! i)))"

definition q1306095_cont_diff_within_order ::
    "nat \<Rightarrow>
      ('e::real_normed_vector \<Rightarrow> 'f::real_normed_vector) \<Rightarrow>
      'e set \<Rightarrow> bool" where
  "q1306095_cont_diff_within_order k f S \<longleftrightarrow>
    (\<exists>D :: nat \<Rightarrow> 'e \<Rightarrow> 'e list \<Rightarrow> 'f.
      (\<forall>x\<in>S. D 0 x [] = f x) \<and>
      (\<forall>j\<le>k. \<forall>x\<in>S. q1306095_multilinear j (D j x)) \<and>
      (\<forall>j<k. \<forall>x\<in>S. \<forall>xs. length xs = j \<longrightarrow>
        ((\<lambda>y. D j y xs) has_derivative
          (\<lambda>h. D (Suc j) x (xs @ [h]))) (at x within S)) \<and>
      (\<forall>xs. length xs = k \<longrightarrow>
        continuous_on S (\<lambda>x. D k x xs)))"

definition q1306095_smooth_within ::
    "('e::real_normed_vector \<Rightarrow> 'f::real_normed_vector) \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q1306095_smooth_within f S \<longleftrightarrow>
    (\<forall>k. q1306095_cont_diff_within_order k f S)"

definition q1306095_model_with_corners ::
    "'e::euclidean_space set \<Rightarrow> bool" where
  "q1306095_model_with_corners H \<longleftrightarrow>
    closed H \<and> convex H \<and> interior H \<noteq> {}"

definition q1306095_valid_manifold ::
    "('m, 'e::euclidean_space, 'c) q1306095_manifold_data \<Rightarrow> bool" where
  "q1306095_valid_manifold A \<longleftrightarrow>
    q1306095_model_with_corners (q1306095_model_carrier A) \<and>
    (\<Union>c. q1306095_chart_source A c) =
      topspace (q1306095_topology A) \<and>
    (\<forall>c. openin (q1306095_topology A) (q1306095_chart_source A c)) \<and>
    (\<forall>c. q1306095_chart_target A c \<subseteq> q1306095_model_carrier A) \<and>
    (\<forall>c. openin (top_of_set (q1306095_model_carrier A))
      (q1306095_chart_target A c)) \<and>
    (\<forall>c. homeomorphic_maps
      (subtopology (q1306095_topology A) (q1306095_chart_source A c))
      (subtopology (top_of_set (q1306095_model_carrier A))
        (q1306095_chart_target A c))
      (q1306095_to_chart A c) (q1306095_from_chart A c)) \<and>
    (\<forall>x\<in>topspace (q1306095_topology A).
      x \<in> q1306095_chart_source A (q1306095_chart_at A x)) \<and>
    (\<forall>a b. q1306095_smooth_within
      (q1306095_to_chart A b \<circ> q1306095_from_chart A a)
      {z \<in> q1306095_chart_target A a.
        q1306095_from_chart A a z \<in> q1306095_chart_source A b})"

definition q1306095_hausdorff ::
    "'a topology \<Rightarrow> bool" where
  "q1306095_hausdorff X \<longleftrightarrow>
    (\<forall>x\<in>topspace X. \<forall>y\<in>topspace X.
      x \<noteq> y \<longrightarrow>
      (\<exists>U V. openin X U \<and> openin X V \<and>
        x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}))"

definition q1306095_euclidean_carrier ::
    "nat \<Rightarrow> (nat \<Rightarrow> real) set" where
  "q1306095_euclidean_carrier n = {v. \<forall>i\<ge>n. v i = 0}"

definition q1306095_euclidean_dist ::
    "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "q1306095_euclidean_dist n x y =
    sqrt (\<Sum>i<n. (x i - y i)\<^sup>2)"

definition q1306095_euclidean_open ::
    "nat \<Rightarrow> (nat \<Rightarrow> real) set \<Rightarrow> bool" where
  "q1306095_euclidean_open n U \<longleftrightarrow>
    U \<subseteq> q1306095_euclidean_carrier n \<and>
    (\<forall>x\<in>U. \<exists>r>0.
      \<forall>y\<in>q1306095_euclidean_carrier n.
        q1306095_euclidean_dist n x y < r \<longrightarrow> y \<in> U)"

definition q1306095_euclidean_topology ::
    "nat \<Rightarrow> (nat \<Rightarrow> real) topology" where
  "q1306095_euclidean_topology n =
    topology (q1306095_euclidean_open n)"

definition q1306095_linear_to_euclidean ::
    "nat \<Rightarrow> ('e::real_normed_vector \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "q1306095_linear_to_euclidean n L \<longleftrightarrow>
    (\<forall>v. L v \<in> q1306095_euclidean_carrier n) \<and>
    (\<forall>u v. L (u + v) = (\<lambda>i. L u i + L v i)) \<and>
    (\<forall>r v. L (r *\<^sub>R v) = (\<lambda>i. r * L v i)) \<and>
    (\<exists>C\<ge>0. \<forall>v.
      q1306095_euclidean_dist n (L v) (\<lambda>i. 0) \<le> C * norm v)"

definition q1306095_smooth_map ::
    "('m, 'e::euclidean_space, 'c) q1306095_manifold_data \<Rightarrow>
      nat \<Rightarrow> ('m \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "q1306095_smooth_map A n e \<longleftrightarrow>
    (\<forall>x\<in>topspace (q1306095_topology A).
      e x \<in> q1306095_euclidean_carrier n) \<and>
    (\<forall>c i. i < n \<longrightarrow>
      q1306095_smooth_within
        (\<lambda>z. e (q1306095_from_chart A c z) i)
        (q1306095_chart_target A c))"

definition q1306095_has_manifold_derivative ::
    "('m, 'e::euclidean_space, 'c) q1306095_manifold_data \<Rightarrow>
      nat \<Rightarrow> ('m \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow>
      'm \<Rightarrow> ('e \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "q1306095_has_manifold_derivative A n e x L \<longleftrightarrow>
    q1306095_linear_to_euclidean n L \<and>
    (\<forall>i. i < n \<longrightarrow>
      ((\<lambda>z. e (q1306095_from_chart A (q1306095_chart_at A x) z) i)
        has_derivative (\<lambda>v. L v i))
       (at (q1306095_to_chart A (q1306095_chart_at A x) x)
        within q1306095_chart_target A (q1306095_chart_at A x)))"

theorem exists_embedding_euclidean_of_compact:
  fixes A :: "('m, 'e::euclidean_space, 'c) q1306095_manifold_data"
  assumes "q1306095_valid_manifold A"
    and "q1306095_hausdorff (q1306095_topology A)"
    and "compact_space (q1306095_topology A)"
  shows "\<exists>n e.
    q1306095_smooth_map A n e \<and>
    embedding_map (q1306095_topology A)
      (q1306095_euclidean_topology n) e \<and>
    closed_map (q1306095_topology A)
      (q1306095_euclidean_topology n) e \<and>
    (\<forall>x\<in>topspace (q1306095_topology A). \<exists>L.
      q1306095_has_manifold_derivative A n e x L \<and> inj L)"
  sorry

end
