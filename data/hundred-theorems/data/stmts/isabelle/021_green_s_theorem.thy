theory Green
  imports Paths Derivs Integrals General_Utils
begin

lemma frontier_Un_subset_Un_frontier:
     "frontier (s \<union> t) \<subseteq> (frontier s) \<union> (frontier t)"
  by sorry

definition has_partial_derivative:: "(('a::euclidean_space) \<Rightarrow> 'b::euclidean_space) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a) \<Rightarrow> bool" where
  "has_partial_derivative F base_vec F' a
        \<equiv> ((\<lambda>x::'a::euclidean_space. F( (a - ((a \<bullet> base_vec) *\<^sub>R base_vec)) + (x \<bullet> base_vec) *\<^sub>R base_vec ))
                has_derivative F') (at a)"

definition has_partial_vector_derivative:: "(('a::euclidean_space) \<Rightarrow> 'b::euclidean_space) \<Rightarrow> 'a \<Rightarrow> ( 'b) \<Rightarrow> ('a) \<Rightarrow> bool" where
  "has_partial_vector_derivative F base_vec F' a
        \<equiv> ((\<lambda>x. F( (a - ((a \<bullet> base_vec) *\<^sub>R base_vec)) + x *\<^sub>R base_vec ))
                has_vector_derivative F') (at (a \<bullet> base_vec))"

definition partially_vector_differentiable where
  "partially_vector_differentiable F base_vec p \<equiv> (\<exists>F'. has_partial_vector_derivative F base_vec F' p)"

definition partial_vector_derivative:: "(('a::euclidean_space) \<Rightarrow> 'b::euclidean_space) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b" where
  "partial_vector_derivative F base_vec a
        \<equiv> (vector_derivative (\<lambda>x. F( (a - ((a \<bullet> base_vec) *\<^sub>R base_vec)) + x *\<^sub>R base_vec)) (at (a \<bullet> base_vec)))"

lemma partial_vector_derivative_works:
  assumes "partially_vector_differentiable F base_vec a"
  shows "has_partial_vector_derivative F base_vec (partial_vector_derivative F base_vec a) a"
  by sorry

lemma fundamental_theorem_of_calculus_partial_vector:
  fixes a b:: "real" and
    F:: "('a::euclidean_space \<Rightarrow> 'b::euclidean_space)" and
    i:: "'a" and
    j:: "'b" and
    F_j_i:: "('a::euclidean_space \<Rightarrow> real)"
  assumes a_leq_b: "a \<le> b" and
    Base_vecs: "i \<in> Basis" "j \<in> Basis" and
    no_i_component: "c \<bullet> i = 0 " and
    has_partial_deriv: "\<forall>p \<in> D. has_partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i (F_j_i p) p" and
    domain_subset_of_D: "{x *\<^sub>R i + c |x. a \<le> x \<and> x \<le> b} \<subseteq> D"
  shows "((\<lambda>x. F_j_i( x *\<^sub>R i + c)) has_integral
          F(b *\<^sub>R i + c) \<bullet> j - F(a *\<^sub>R i + c) \<bullet> j) (cbox a b)"
  by sorry

lemma fundamental_theorem_of_calculus_partial_vector_gen:
  fixes k1 k2:: "real" and
    F:: "('a::euclidean_space \<Rightarrow> 'b::euclidean_space)" and
    i:: "'a" and
    F_i:: "('a::euclidean_space \<Rightarrow> 'b)"
  assumes a_leq_b: "k1 \<le> k2" and
    unit_len: "i \<bullet> i = 1" and
    no_i_component: "c \<bullet> i = 0 " and
    has_partial_deriv: "\<forall>p \<in> D. has_partial_vector_derivative F i (F_i p) p" and
    domain_subset_of_D: "{v. \<exists>x. k1 \<le> x \<and> x \<le> k2 \<and> v = x *\<^sub>R i + c} \<subseteq> D"
  shows "( (\<lambda>x. F_i( x *\<^sub>R i + c)) has_integral
                                        F(k2 *\<^sub>R i + c) - F(k1 *\<^sub>R i + c)) (cbox k1 k2)"
  by sorry

lemma add_scale_img:
  assumes "a < b" shows "(\<lambda>x::real. a + (b - a) * x) ` {0 .. 1} = {a .. b}"
  by sorry

lemma add_scale_img':
  assumes "a \<le> b"
  shows "(\<lambda>x::real. a + (b - a) * x) ` {0 .. 1} = {a .. b}"
  by sorry

definition analytically_valid:: "'a::euclidean_space set \<Rightarrow> ('a \<Rightarrow> 'b::{euclidean_space,times,zero_neq_one}) \<Rightarrow> 'a \<Rightarrow> bool" where
  "analytically_valid s F i \<equiv>
       (\<forall>a \<in> s. partially_vector_differentiable F i a) \<and>
       continuous_on s F \<and> \<comment> \<open>TODO: should we replace this with saying that \<open>F\<close> is partially diffrerentiable on \<open>Dy\<close>,\<close>
                           \<comment> \<open>i.e. there is a partial derivative on every dimension\<close>
       integrable lborel (\<lambda>p. (partial_vector_derivative F i) p * indicator s p) \<and>
       (\<lambda>x. integral UNIV (\<lambda>y. (partial_vector_derivative F i (y *\<^sub>R i + x *\<^sub>R (\<Sum> b \<in>(Basis - {i}). b)))
            * (indicator s (y *\<^sub>R i + x *\<^sub>R (\<Sum>b \<in> Basis - {i}. b)) ))) \<in> borel_measurable lborel"
  (*(\<lambda>x. integral UNIV (\<lambda>y. ((partial_vector_derivative F i) (y, x)) * (indicator s (y, x)))) \<in> borel_measurable lborel)"*)


lemma analytically_valid_imp_part_deriv_integrable_on:
  assumes "analytically_valid (s::(real*real) set) (f::(real*real)\<Rightarrow> real) i"
  shows "(partial_vector_derivative f i) integrable_on s"
  by sorry

(*******************************************************************************)

definition typeII_twoCube :: "((real * real) \<Rightarrow> (real * real)) \<Rightarrow> bool" where
  "typeII_twoCube twoC
         \<equiv> \<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a..b}. g2 x \<le> g1 x) \<and>
                       twoC = (\<lambda>(y, x). ((1 - y) * (g2 ((1-x)*a + x*b)) + y * (g1 ((1-x)*a + x*b)),
                                        (1-x)*a + x*b)) \<and>
                       g1 piecewise_C1_differentiable_on {a .. b} \<and>
                       g2 piecewise_C1_differentiable_on {a .. b}"

abbreviation unit_cube where "unit_cube \<equiv> cbox (0,0) (1::real,1::real)" 

definition cubeImage:: "two_cube \<Rightarrow> ((real*real) set)" where
  "cubeImage twoC \<equiv> (twoC ` unit_cube)"

lemma typeII_twoCubeImg:
  assumes "typeII_twoCube twoC"
  shows "\<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a .. b}. g2 x \<le> g1 x) \<and>
                      cubeImage twoC = {(y,x). x \<in> {a..b} \<and> y \<in> {g2 x .. g1 x}}
                      \<and> twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))
                      \<and> g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b} "
  by sorry

definition horizontal_boundary :: "two_cube \<Rightarrow> one_chain" where
  "horizontal_boundary twoC \<equiv> {(1, (\<lambda>x. twoC(x,0))), (-1, (\<lambda>x. twoC(x,1)))}"

definition vertical_boundary :: "two_cube \<Rightarrow> one_chain" where
  "vertical_boundary twoC \<equiv> {(-1, (\<lambda>y. twoC(0,y))), (1, (\<lambda>y. twoC(1,y)))}"

definition boundary :: "two_cube \<Rightarrow> one_chain" where
  "boundary twoC \<equiv> horizontal_boundary twoC \<union> vertical_boundary twoC"

definition valid_two_cube where
  "valid_two_cube twoC \<equiv> card (boundary twoC) = 4"

definition two_chain_integral:: "two_chain \<Rightarrow> ((real*real)\<Rightarrow>(real)) \<Rightarrow> real" where
  "two_chain_integral twoChain F \<equiv> \<Sum>C\<in>twoChain. (integral (cubeImage C) F)"

definition valid_two_chain where
  "valid_two_chain twoChain \<equiv> (\<forall>twoCube \<in> twoChain. valid_two_cube twoCube) \<and> pairwise (\<lambda>c1 c2. ((boundary c1) \<inter> (boundary c2)) = {}) twoChain \<and> inj_on cubeImage twoChain"

definition two_chain_boundary:: "two_chain \<Rightarrow> one_chain" where
  "two_chain_boundary twoChain == \<Union>(boundary ` twoChain)"

definition gen_division where
  "gen_division s S \<equiv> (finite S \<and> (\<Union>S = s) \<and> pairwise (\<lambda>X Y. negligible (X \<inter> Y)) S)"


definition two_chain_horizontal_boundary:: "two_chain \<Rightarrow> one_chain" where
  "two_chain_horizontal_boundary twoChain  \<equiv> \<Union>(horizontal_boundary ` twoChain)"

definition two_chain_vertical_boundary:: "two_chain \<Rightarrow> one_chain" where
  "two_chain_vertical_boundary twoChain  \<equiv> \<Union>(vertical_boundary ` twoChain)"

definition only_horizontal_division where
  "only_horizontal_division one_chain two_chain 
      \<equiv> \<exists>\<H> \<V>. finite \<H> \<and> finite \<V> \<and>
               (\<forall>(k,\<gamma>) \<in> \<H>.
                 (\<exists>(k', \<gamma>') \<in> two_chain_horizontal_boundary two_chain.
                     (\<exists>a \<in> {0..1}. \<exists>b \<in> {0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>))) \<and>
               (common_sudiv_exists (two_chain_vertical_boundary two_chain) \<V>
                \<or> common_reparam_exists \<V> (two_chain_vertical_boundary two_chain)) \<and>
               boundary_chain \<V> \<and>
               one_chain = \<H> \<union> \<V> \<and> (\<forall>(k,\<gamma>)\<in>\<V>. valid_path \<gamma>)"

lemma sum_zero_set:
  assumes "\<forall>x \<in> s. f x = 0" "finite s" "finite t"
  shows "sum f (s \<union> t) = sum f t"
  by sorry

abbreviation "valid_typeII_division s twoChain \<equiv> ((\<forall>twoCube \<in> twoChain. typeII_twoCube twoCube) \<and>
                                                (gen_division s (cubeImage ` twoChain)) \<and>
                                                (valid_two_chain twoChain))"

lemma two_chain_vertical_boundary_is_boundary_chain:
  shows "boundary_chain (two_chain_vertical_boundary twoChain)"
  by sorry

lemma two_chain_horizontal_boundary_is_boundary_chain:
  shows "boundary_chain (two_chain_horizontal_boundary twoChain)"
  by sorry

definition typeI_twoCube :: "two_cube \<Rightarrow> bool" where
  "typeI_twoCube (twoC::two_cube)
        \<equiv> \<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a..b}. g2 x \<le> g1 x) \<and>
                       twoC = (\<lambda>(x,y). ((1-x)*a + x*b,
                                        (1 - y) * (g2 ((1-x)*a + x*b)) + y * (g1 ((1-x)*a + x*b)))) \<and>
                       g1 piecewise_C1_differentiable_on {a..b} \<and>
                       g2 piecewise_C1_differentiable_on {a..b}"

lemma typeI_twoCubeImg:
  assumes "typeI_twoCube twoC"
  shows "\<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a .. b}. g2 x \<le> g1 x) \<and>
                      cubeImage twoC = {(x,y). x \<in> {a..b} \<and> y \<in> {g2 x .. g1 x}} \<and>
                      twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b))) \<and>
                      g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b} "
  by sorry

lemma typeI_cube_explicit_spec:
  assumes "typeI_twoCube twoC"
  shows "\<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a .. b}. g2 x \<le> g1 x) \<and>
                      cubeImage twoC = {(x,y). x \<in> {a..b} \<and> y \<in> {g2 x .. g1 x}}
                      \<and> twoC = (\<lambda>(x, y). ((1 - x) * a + x * b, (1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b)))
                      \<and> g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b}
                      \<and> (\<lambda>x. twoC(x, 0)) = (\<lambda>x. (a + (b - a) * x, g2 (a + (b - a) * x)))
                      \<and> (\<lambda>y. twoC(1, y)) = (\<lambda>x. (b, g2 b + x *\<^sub>R (g1 b - g2 b)))
                      \<and> (\<lambda>x. twoC(x, 1)) = (\<lambda>x. (a + (b - a) * x, g1 (a + (b - a) * x)))
                      \<and> (\<lambda>y. twoC(0, y)) = (\<lambda>x. (a, g2 a + x *\<^sub>R (g1 a - g2 a)))"
  by sorry

lemma typeI_twoCube_smooth_edges:
  assumes "typeI_twoCube twoC"
    "(k,\<gamma>) \<in> boundary twoC"
  shows "\<gamma> piecewise_C1_differentiable_on {0..1}"
  by sorry

lemma two_chain_integral_eq_integral_divisable:
  assumes f_integrable: "\<forall>twoCube \<in> twoChain. F integrable_on cubeImage twoCube" and
    gen_division: "gen_division s (cubeImage ` twoChain)" and
    valid_two_chain: "valid_two_chain twoChain"
  shows "integral s F = two_chain_integral twoChain F"
  by sorry

definition only_vertical_division where
  "only_vertical_division one_chain two_chain \<equiv>
       \<exists>\<V> \<H>. finite \<H> \<and> finite \<V> \<and>
               (\<forall>(k,\<gamma>) \<in> \<V>.
                 (\<exists>(k',\<gamma>') \<in> two_chain_vertical_boundary two_chain.
                     (\<exists>a \<in> {0..1}. \<exists>b \<in> {0..1}. a \<le> b \<and> subpath a b \<gamma>' = \<gamma>))) \<and>
               (common_sudiv_exists (two_chain_horizontal_boundary two_chain) \<H>
                \<or> common_reparam_exists \<H> (two_chain_horizontal_boundary two_chain)) \<and>
               boundary_chain \<H> \<and> one_chain = \<V> \<union> \<H> \<and>
               (\<forall>(k,\<gamma>)\<in>\<H>. valid_path \<gamma>)"

abbreviation "valid_typeI_division s twoChain 
   \<equiv> (\<forall>twoCube \<in> twoChain. typeI_twoCube twoCube) \<and>
      gen_division s (cubeImage ` twoChain) \<and> valid_two_chain twoChain"


lemma field_cont_on_typeI_region_cont_on_edges:
  assumes typeI_twoC: "typeI_twoCube twoC" 
    and field_cont: "continuous_on (cubeImage twoC) F" 
    and member_of_boundary: "(k,\<gamma>) \<in> boundary twoC"
  shows "continuous_on (\<gamma> ` {0 .. 1}) F"
  by sorry

lemma typeII_cube_explicit_spec:
  assumes "typeII_twoCube twoC"
  shows "\<exists>a b g1 g2. a < b \<and> (\<forall>x \<in> {a .. b}. g2 x \<le> g1 x) \<and>
                     cubeImage twoC = {(y, x). x \<in> {a..b} \<and> y \<in> {g2 x .. g1 x}}
                  \<and> twoC = (\<lambda>(y, x). ((1 - y) * g2 ((1 - x) * a + x * b) + y * g1 ((1 - x) * a + x * b), (1 - x) * a + x * b))
                  \<and> g1 piecewise_C1_differentiable_on {a .. b} \<and> g2 piecewise_C1_differentiable_on {a .. b}
                  \<and> (\<lambda>x. twoC(0, x)) = (\<lambda>x. (g2 (a + (b - a) * x), a + (b - a) * x))
                  \<and> (\<lambda>y. twoC(y, 1)) = (\<lambda>x. (g2 b + x *\<^sub>R (g1 b - g2 b), b))
                  \<and> (\<lambda>x. twoC(1, x)) = (\<lambda>x. (g1 (a + (b - a) * x), a + (b - a) * x))
                  \<and> (\<lambda>y. twoC(y, 0)) = (\<lambda>x. (g2 a + x *\<^sub>R (g1 a - g2 a), a))"
  by sorry

lemma typeII_twoCube_smooth_edges:
  assumes "typeII_twoCube twoC" "(k,\<gamma>) \<in> boundary twoC"
  shows "\<gamma> piecewise_C1_differentiable_on {0..1}"
  by sorry

lemma field_cont_on_typeII_region_cont_on_edges:
  assumes typeII_twoC:
    "typeII_twoCube twoC" and
    field_cont:
    "continuous_on (cubeImage twoC) F" and
    member_of_boundary:
    "(k,\<gamma>) \<in> boundary twoC"
  shows "continuous_on (\<gamma> ` {0 .. 1}) F"
  by sorry

lemma two_cube_boundary_is_boundary: "boundary_chain (boundary C)"
  by sorry

lemma common_boundary_subdiv_exists_refl:
  assumes "\<forall>(k,\<gamma>)\<in>boundary twoC. valid_path \<gamma>"
  shows "common_boundary_sudivision_exists (boundary twoC) (boundary twoC)"
  by sorry

lemma common_boundary_subdiv_exists_refl':
  assumes "\<forall>(k,\<gamma>)\<in>C. valid_path \<gamma>"
    "boundary_chain (C::(int \<times> (real \<Rightarrow> real \<times> real)) set)"
  shows "common_boundary_sudivision_exists (C) (C)"
  by sorry

lemma gen_common_boundary_subdiv_exists_refl_twochain_boundary:
  assumes "\<forall>(k,\<gamma>)\<in>C. valid_path \<gamma>"
    "boundary_chain (C::(int \<times> (real \<Rightarrow> real \<times> real)) set)"
  shows "common_sudiv_exists (C) (C)"
  by sorry

lemma two_chain_boundary_is_boundary_chain:
  shows "boundary_chain (two_chain_boundary twoChain)"
  by sorry

lemma typeI_edges_are_valid_paths:
  assumes "typeI_twoCube twoC" "(k,\<gamma>) \<in> boundary twoC"
  shows "valid_path \<gamma>"
  by sorry

lemma typeII_edges_are_valid_paths:
  assumes "typeII_twoCube twoC" "(k,\<gamma>) \<in> boundary twoC"
  shows "valid_path \<gamma>"
  by sorry

lemma finite_two_chain_vertical_boundary:
  assumes "finite two_chain"
  shows "finite (two_chain_vertical_boundary two_chain)"
  by sorry

lemma finite_two_chain_horizontal_boundary:
  assumes "finite two_chain"
  shows "finite (two_chain_horizontal_boundary two_chain)"
  by sorry

locale R2 =
  fixes i j
  assumes i_is_x_axis: "i = (1::real,0::real)" and
    j_is_y_axis: "j = (0::real, 1::real)"
begin

lemma analytically_valid_y:
  assumes "analytically_valid s F i"
  shows "(\<lambda>x. integral UNIV (\<lambda>y. (partial_vector_derivative F i) (y, x) * (indicator s (y, x)))) \<in> borel_measurable lborel"
  by sorry

lemma analytically_valid_x:
  assumes "analytically_valid s F j"
  shows "(\<lambda>x. integral UNIV (\<lambda>y. ((partial_vector_derivative F j) (x, y)) * (indicator s (x, y)))) \<in> borel_measurable lborel"
  by sorry

lemma Greens_thm_type_I:
  fixes F:: "((real*real) \<Rightarrow> (real * real))" and
    gamma1 gamma2 gamma3 gamma4 :: "(real \<Rightarrow> (real * real))" and
    a:: "real" and b:: "real" and
    g1:: "(real \<Rightarrow> real)" and g2:: "(real \<Rightarrow> real)"
  assumes Dy_def: "Dy_pair = {(x::real,y) . x \<in> cbox a b \<and> y \<in> cbox (g2 x) (g1 x)}" and
    gamma1_def: "gamma1 = (\<lambda>x. (a + (b - a) * x, g2(a + (b - a) * x)))" and
    gamma1_smooth: "gamma1 piecewise_C1_differentiable_on {0..1}" and (*TODO: This should be piecewise smooth*)
    gamma2_def: "gamma2 = (\<lambda>x. (b, g2(b) + x  *\<^sub>R (g1(b) - g2(b))))" and
    gamma3_def: "gamma3 = (\<lambda>x. (a + (b - a) * x, g1(a + (b - a) * x)))" and
    gamma3_smooth: "gamma3 piecewise_C1_differentiable_on {0..1}" and
    gamma4_def: "gamma4 = (\<lambda>x. (a,  g2(a) + x *\<^sub>R (g1(a) - g2(a))))" and
    F_i_analytically_valid: "analytically_valid Dy_pair (\<lambda>p. F(p) \<bullet> i) j" and
    g2_leq_g1: "\<forall>x \<in> cbox a b. (g2 x) \<le> (g1 x)" and (*This is needed otherwise what would Dy be?*)
    a_lt_b: "a < b"
  shows "(line_integral F {i} gamma1) +
         (line_integral F {i} gamma2) -
         (line_integral F {i} gamma3) -
         (line_integral F {i} gamma4)
                 = (integral Dy_pair (\<lambda>a. - (partial_vector_derivative (\<lambda>p. F(p) \<bullet> i) j a)))"
    "line_integral_exists F {i} gamma4"
    "line_integral_exists F {i} gamma3"
    "line_integral_exists F {i} gamma2"
    "line_integral_exists F {i} gamma1"
  by sorry

theorem Greens_thm_type_II:
  fixes F:: "((real*real) \<Rightarrow> (real * real))" and
    gamma4 gamma3 gamma2 gamma1 :: "(real \<Rightarrow> (real * real))" and
    a:: "real" and b:: "real" and
    g1:: "(real \<Rightarrow> real)" and g2:: "(real \<Rightarrow> real)"
  assumes Dx_def: "Dx_pair = {(x::real,y) . y \<in> cbox a b \<and> x \<in> cbox (g2 y) (g1 y)}" and
    gamma4_def: "gamma4 = (\<lambda>x. (g2(a + (b - a) * x), a + (b - a) * x))" and
    gamma4_smooth: "gamma4 piecewise_C1_differentiable_on {0..1}" and (*TODO: This should be piecewise smooth*)
    gamma3_def: "gamma3 = (\<lambda>x. (g2(b) + x  *\<^sub>R (g1(b) - g2(b)), b))" and
    gamma2_def: "gamma2 = (\<lambda>x. (g1(a + (b - a) * x), a + (b - a) * x))" and
    gamma2_smooth: "gamma2 piecewise_C1_differentiable_on {0..1}" and
    gamma1_def: "gamma1 = (\<lambda>x. (g2(a) + x *\<^sub>R (g1(a) - g2(a)), a))" and
    F_j_analytically_valid: "analytically_valid Dx_pair (\<lambda>p. F(p) \<bullet> j) i" and
    g2_leq_g1: "\<forall>x \<in> cbox a b. (g2 x) \<le> (g1 x)" and (*This is needed otherwise what would Dy be?*)
    a_lt_b: "a < b"
  shows "-(line_integral F {j} gamma4) -
         (line_integral F {j} gamma3) +
         (line_integral F {j} gamma2) +
         (line_integral F {j} gamma1)
                 = (integral Dx_pair (\<lambda>a. (partial_vector_derivative (\<lambda>a. (F a) \<bullet> j)  i a)))"
    "line_integral_exists F {j} gamma4"
    "line_integral_exists F {j} gamma3"
    "line_integral_exists F {j} gamma2"
    "line_integral_exists F {j} gamma1"
  by sorry

end

locale green_typeII_cube =  R2 + 
  fixes twoC F
  assumes 
    two_cube: "typeII_twoCube twoC" and
    valid_two_cube: "valid_two_cube twoC" and
    f_analytically_valid: "analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> j) i"
begin

lemma GreenThm_typeII_twoCube:
  shows "integral (cubeImage twoC) (\<lambda>a. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i  a) = one_chain_line_integral F {j} (boundary twoC)"
    "\<forall>(k,\<gamma>) \<in> boundary twoC. line_integral_exists F {j} \<gamma>"
  by sorry

lemma line_integral_exists_on_typeII_Cube_boundaries':
  assumes "(k,\<gamma>) \<in> boundary twoC"
  shows "line_integral_exists F {j} \<gamma>"
  by sorry

end

locale green_typeII_chain =  R2 + 
  fixes F two_chain s
  assumes valid_typeII_div: "valid_typeII_division s two_chain" and
          F_anal_valid: "\<forall>twoC \<in> two_chain. analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> j) i"
begin

lemma two_chain_valid_valid_cubes: "\<forall>two_cube \<in> two_chain. valid_two_cube two_cube" using valid_typeII_div
  by sorry

lemma typeII_chain_line_integral_exists_boundary':
  shows "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. line_integral_exists F {j} \<gamma>"
  by sorry

lemma typeII_chain_line_integral_exists_boundary'':
     "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. line_integral_exists F {j} \<gamma>"
  by sorry

lemma typeII_cube_line_integral_exists_boundary:
     "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {j} \<gamma>"
  by sorry

lemma type_II_chain_horiz_bound_valid:
     "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. valid_path \<gamma>"
  by sorry

lemma type_II_chain_vert_bound_valid: (*This and the previous one need to be used in all proofs*)
     "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. valid_path \<gamma>"
  by sorry

lemma members_of_only_horiz_div_line_integrable':
  assumes "only_horizontal_division one_chain two_chain"
    "(k::int, \<gamma>)\<in>one_chain"
    "(k::int, \<gamma>)\<in>one_chain"
    "finite two_chain"
    "\<forall>two_cube \<in> two_chain. valid_two_cube two_cube"
  shows "line_integral_exists F {j} \<gamma>"
  by sorry

lemma GreenThm_typeII_twoChain:
  shows "two_chain_integral two_chain (partial_vector_derivative (\<lambda>a. (F a) \<bullet> j)  i) = one_chain_line_integral F {j} (two_chain_boundary two_chain)"
  by sorry

lemma GreenThm_typeII_divisible:
  assumes 
    gen_division: "gen_division s (cubeImage ` two_chain)"    (*This should follow from the assumption that images are not negligible*)
  shows "integral s (partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i) = one_chain_line_integral F {j} (two_chain_boundary two_chain)"
  by sorry

lemma GreenThm_typeII_divisible_region_boundary_gen:
  assumes only_horizontal_division: "only_horizontal_division \<gamma> two_chain"
  shows "integral s (partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i) = one_chain_line_integral F {j} \<gamma>"
  by sorry

lemma GreenThm_typeII_divisible_region_boundary:
  assumes
    two_cubes_trace_vertical_boundaries: 
    "two_chain_vertical_boundary two_chain \<subseteq> \<gamma>" and
    boundary_of_region_is_subset_of_partition_boundary:
    "\<gamma> \<subseteq> two_chain_boundary two_chain"
  shows "integral s (partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i) = one_chain_line_integral F {j} \<gamma>"
  by sorry

end

locale green_typeI_cube =  R2 +
  fixes twoC F
  assumes 
    two_cube: "typeI_twoCube twoC" and
    valid_two_cube: "valid_two_cube twoC" and
    f_analytically_valid: "analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> i) j"
begin

lemma GreenThm_typeI_twoCube:
  shows "integral (cubeImage twoC) (\<lambda>a. - partial_vector_derivative (\<lambda>p. F p \<bullet> i) j  a) = one_chain_line_integral F {i} (boundary twoC)"
    "\<forall>(k,\<gamma>) \<in> boundary twoC. line_integral_exists F {i} \<gamma>"
  by sorry

lemma line_integral_exists_on_typeI_Cube_boundaries':
  assumes "(k,\<gamma>) \<in> boundary twoC"
  shows "line_integral_exists F {i} \<gamma>"
  by sorry

end

locale green_typeI_chain = R2 + 
  fixes F two_chain s
  assumes valid_typeI_div: "valid_typeI_division s two_chain" and
          F_anal_valid: "\<forall>twoC \<in> two_chain. analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> i) j"
begin

lemma two_chain_valid_valid_cubes: "\<forall>two_cube \<in> two_chain. valid_two_cube two_cube" using valid_typeI_div
  by sorry

lemma typeI_cube_line_integral_exists_boundary':
  assumes "\<forall>two_cube \<in> two_chain. typeI_twoCube two_cube"
  assumes "\<forall>twoC \<in> two_chain. analytically_valid (cubeImage twoC) (\<lambda>x. (F x) \<bullet> i) j"
  assumes "\<forall>two_cube \<in> two_chain. valid_two_cube two_cube"
  shows "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. line_integral_exists F {i} \<gamma>"
  by sorry

lemma typeI_cube_line_integral_exists_boundary'':
  "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. line_integral_exists F {i} \<gamma>"
  by sorry

lemma typeI_cube_line_integral_exists_boundary:
  "\<forall>(k,\<gamma>) \<in> two_chain_boundary two_chain. line_integral_exists F {i} \<gamma>"
  by sorry

lemma type_I_chain_horiz_bound_valid:
  "\<forall>(k,\<gamma>) \<in> two_chain_horizontal_boundary two_chain. valid_path \<gamma>"
  by sorry

lemma type_I_chain_vert_bound_valid: (*This and the previous one need to be used in all proofs*)
  assumes "\<forall>two_cube \<in> two_chain. typeI_twoCube two_cube"
  shows "\<forall>(k,\<gamma>) \<in> two_chain_vertical_boundary two_chain. valid_path \<gamma>"
  by sorry

lemma members_of_only_vertical_div_line_integrable':
  assumes "only_vertical_division one_chain two_chain"
    "(k::int, \<gamma>)\<in>one_chain"
    "(k::int, \<gamma>)\<in>one_chain"
    "finite two_chain"
  shows "line_integral_exists F {i} \<gamma>"
  by sorry

lemma GreenThm_typeI_two_chain:
   "two_chain_integral two_chain (\<lambda>a. - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j a) = one_chain_line_integral F {i} (two_chain_boundary two_chain)"
  by sorry

lemma GreenThm_typeI_divisible:
  assumes gen_division: "gen_division s (cubeImage ` two_chain)"
  shows "integral s (\<lambda>x. - partial_vector_derivative (\<lambda>a. F(a) \<bullet> i) j x) = one_chain_line_integral F {i} (two_chain_boundary two_chain)"
  by sorry

lemma GreenThm_typeI_divisible_region_boundary:
  assumes 
    gen_division: "gen_division s (cubeImage ` two_chain)" and
    two_cubes_trace_horizontal_boundaries:
    "two_chain_horizontal_boundary two_chain \<subseteq> \<gamma>" and
    boundary_of_region_is_subset_of_partition_boundary:
    "\<gamma> \<subseteq> two_chain_boundary two_chain"
  shows "integral s (\<lambda>x. - partial_vector_derivative (\<lambda>a. F(a) \<bullet> i) j x) = one_chain_line_integral F {i} \<gamma>"
  by sorry

lemma GreenThm_typeI_divisible_region_boundary_gen:
  assumes valid_typeI_div: "valid_typeI_division s two_chain" and
    f_analytically_valid: "\<forall>twoC \<in> two_chain. analytically_valid (cubeImage twoC) (\<lambda>a. F(a) \<bullet> i) j" and
    only_vertical_division:
    "only_vertical_division \<gamma> two_chain"
  shows "integral s (\<lambda>x. - partial_vector_derivative (\<lambda>a. F(a) \<bullet> i) j x) = one_chain_line_integral F {i} \<gamma>"
  by sorry

end

locale green_typeI_typeII_chain = R2: R2 i j + T1: green_typeI_chain i j F two_chain_typeI + T2: green_typeII_chain i j F two_chain_typeII for i j F two_chain_typeI two_chain_typeII
begin

lemma GreenThm_typeI_typeII_divisible_region_boundary:
  assumes 
    gen_divisions: "gen_division s (cubeImage ` two_chain_typeI)"
    "gen_division s (cubeImage ` two_chain_typeII)" and
    typeI_two_cubes_trace_horizontal_boundaries:
    "two_chain_horizontal_boundary two_chain_typeI \<subseteq> \<gamma>" and
    typeII_two_cubes_trace_vertical_boundaries:
    "two_chain_vertical_boundary two_chain_typeII \<subseteq> \<gamma>" and
    boundary_of_region_is_subset_of_partition_boundaries:
    "\<gamma> \<subseteq> two_chain_boundary two_chain_typeI"
    "\<gamma> \<subseteq> two_chain_boundary two_chain_typeII"
  shows "integral s (\<lambda>x. partial_vector_derivative (\<lambda>a. F a \<bullet> j) i x - partial_vector_derivative (\<lambda>a. F a \<bullet> i) j x)
         = one_chain_line_integral F {i, j} \<gamma>"
  by sorry

lemma GreenThm_typeI_typeII_divisible_region':
  assumes 
    only_vertical_division:
    "only_vertical_division one_chain_typeI two_chain_typeI"
    "boundary_chain one_chain_typeI" and
    only_horizontal_division:
    "only_horizontal_division one_chain_typeII two_chain_typeII"
    "boundary_chain one_chain_typeII" and
    typeI_and_typII_one_chains_have_gen_common_subdiv:
    "common_sudiv_exists one_chain_typeI one_chain_typeII"
  shows "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeI"
    "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeII"
  by sorry

lemma GreenThm_typeI_typeII_divisible_region:
  assumes only_vertical_division:
    "only_vertical_division one_chain_typeI two_chain_typeI"
    "boundary_chain one_chain_typeI" and
    only_horizontal_division:
    "only_horizontal_division one_chain_typeII two_chain_typeII"
    "boundary_chain one_chain_typeII" and
    typeI_and_typII_one_chains_have_common_subdiv:
    "common_boundary_sudivision_exists one_chain_typeI one_chain_typeII"
  shows "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeI"
    "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeII"
  by sorry

lemma GreenThm_typeI_typeII_divisible_region_finite_holes:
  assumes valid_cube_boundary: "\<forall>(k,\<gamma>)\<in>boundary C. valid_path \<gamma>" and
    only_vertical_division:
    "only_vertical_division (boundary C) two_chain_typeI" and
    only_horizontal_division:
    "only_horizontal_division (boundary C) two_chain_typeII" and
    s_is_oneCube: "s = cubeImage C"
  shows "integral (cubeImage C) (\<lambda>x. partial_vector_derivative (\<lambda>x. F x \<bullet> j) i x - partial_vector_derivative (\<lambda>x. F x \<bullet> i) j x) =
                     one_chain_line_integral F {i, j} (boundary C)"
  by sorry

lemma GreenThm_typeI_typeII_divisible_region_equivallent_boundary:
  assumes 
    gen_divisions: "gen_division s (cubeImage ` two_chain_typeI)"
    "gen_division s (cubeImage ` two_chain_typeII)" and
    typeI_two_cubes_trace_horizontal_boundaries:
    "two_chain_horizontal_boundary two_chain_typeI \<subseteq> one_chain_typeI" and
    typeII_two_cubes_trace_vertical_boundaries:
    "two_chain_vertical_boundary two_chain_typeII \<subseteq> one_chain_typeII" and
    boundary_of_region_is_subset_of_partition_boundaries:
    "one_chain_typeI \<subseteq> two_chain_boundary two_chain_typeI"
    "one_chain_typeII \<subseteq> two_chain_boundary two_chain_typeII" and
    typeI_and_typII_one_chains_have_common_subdiv:
    "common_boundary_sudivision_exists one_chain_typeI one_chain_typeII"
  shows "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeI"
    "integral s (\<lambda>x. partial_vector_derivative (\<lambda>x. (F x) \<bullet> j) i x - partial_vector_derivative (\<lambda>x. (F x) \<bullet> i) j x) = one_chain_line_integral F {i, j} one_chain_typeII"
  by sorry

end
end
