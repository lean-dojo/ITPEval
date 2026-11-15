(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

chapter \<open>Vector Analysis\<close>

theory Topology_Euclidean_Space
  imports
    Elementary_Normed_Spaces
    Linear_Algebra
    Norm_Arith
begin

section \<open>Elementary Topology in Euclidean Space\<close>

lemma euclidean_dist_l2:
  fixes x y :: "'a :: euclidean_space"
  shows "dist x y = L2_set (\<lambda>i. dist (x \<bullet> i) (y \<bullet> i)) Basis"
  by sorry

lemma norm_nth_le: "norm (x \<bullet> i) \<le> norm x" if "i \<in> Basis"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Continuity of the representation WRT an orthogonal basis\<close>

lemma orthogonal_Basis: "pairwise orthogonal Basis"
  by sorry

lemma representation_bound:
  fixes B :: "'N::real_inner set"
  assumes "finite B" "independent B" "b \<in> B" and orth: "pairwise orthogonal B"
  obtains m where "m > 0" "\<And>x. x \<in> span B \<Longrightarrow> \<bar>representation B x b\<bar> \<le> m * norm x"
  by sorry

lemma continuous_on_representation:
  fixes B :: "'N::euclidean_space set"
  assumes "finite B" "independent B" "b \<in> B" "pairwise orthogonal B" 
  shows "continuous_on (span B) (\<lambda>x. representation B x b)"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Balls in Euclidean Space\<close>

lemma cball_subset_cball_iff:
  fixes a :: "'a :: euclidean_space"
  shows "cball a r \<subseteq> cball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r < 0"
    (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma cball_subset_ball_iff: "cball a r \<subseteq> ball a' r' \<longleftrightarrow> dist a a' + r < r' \<or> r < 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for a :: "'a::euclidean_space"
  by sorry

lemma ball_subset_cball_iff: "ball a r \<subseteq> cball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r \<le> 0"
  (is "?lhs = ?rhs")
  for a :: "'a::euclidean_space"
  by sorry

lemma ball_subset_ball_iff:
  fixes a :: "'a :: euclidean_space"
  shows "ball a r \<subseteq> ball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r \<le> 0"
        (is "?lhs = ?rhs")
  by sorry


lemma ball_eq_ball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "ball x d = ball y e \<longleftrightarrow> d \<le> 0 \<and> e \<le> 0 \<or> x=y \<and> d=e"
  by sorry

lemma cball_eq_cball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "cball x d = cball y e \<longleftrightarrow> d < 0 \<and> e < 0 \<or> x=y \<and> d=e"
  by sorry

lemma ball_eq_cball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "ball x d = cball y e \<longleftrightarrow> d \<le> 0 \<and> e < 0" (is "?lhs = ?rhs")
  by sorry

lemma cball_eq_ball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "cball x d = ball y e \<longleftrightarrow> d < 0 \<and> e \<le> 0"
  by sorry

lemma finite_ball_avoid:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "finite X" "p \<in> S"
  shows "\<exists>e>0. \<forall>w\<in>ball p e. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
  by sorry

lemma finite_cball_avoid:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "finite X" "p \<in> S"
  shows "\<exists>e>0. \<forall>w\<in>cball p e. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
  by sorry

lemma dim_cball:
  assumes "e > 0"
  shows "dim (cball (0 :: 'n::euclidean_space) e) = DIM('n)"
  by sorry


subsection \<open>Boxes\<close>

abbreviation\<^marker>\<open>tag important\<close> One :: "'a::euclidean_space" where
"One \<equiv> \<Sum>Basis"

lemma One_non_0: assumes "One = (0::'a::euclidean_space)" shows False
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> One_neq_0[iff]: "One \<noteq> 0"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> Zero_neq_One[iff]: "0 \<noteq> One"
  by sorry

definition\<^marker>\<open>tag important\<close> (in euclidean_space) eucl_less (infix \<open><e\<close> 50) where 
"eucl_less a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i)"

definition\<^marker>\<open>tag important\<close> box_eucl_less: "box a b = {x. a <e x \<and> x <e b}"
definition\<^marker>\<open>tag important\<close> "cbox a b = {x. \<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i}"

lemma box_def: "box a b = {x. \<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i}"
  and in_box_eucl_less: "x \<in> box a b \<longleftrightarrow> a <e x \<and> x <e b"
  and mem_box: "x \<in> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i)"
    "x \<in> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i)"
  by sorry

lemma cbox_Pair_eq: "cbox (a, c) (b, d) = cbox a b \<times> cbox c d"
  by sorry

lemma cbox_Pair_iff [iff]: "(x, y) \<in> cbox (a, c) (b, d) \<longleftrightarrow> x \<in> cbox a b \<and> y \<in> cbox c d"
  by sorry

lemma cbox_Complex_eq: "cbox (Complex a c) (Complex b d) = (\<lambda>(x,y). Complex x y) ` (cbox a b \<times> cbox c d)"
  by sorry

lemma cbox_Pair_eq_0: "cbox (a, c) (b, d) = {} \<longleftrightarrow> cbox a b = {} \<or> cbox c d = {}"
  by sorry

lemma swap_cbox_Pair [simp]: "prod.swap ` cbox (c, a) (d, b) = cbox (a,c) (b,d)"
  by sorry

lemma mem_box_real[simp]:
  "(x::real) \<in> box a b \<longleftrightarrow> a < x \<and> x < b"
  "(x::real) \<in> cbox a b \<longleftrightarrow> a \<le> x \<and> x \<le> b"
  by sorry

lemma box_real[simp]:
  fixes a b:: real
  shows "box a b = {a <..< b}" "cbox a b = {a .. b}"
  by sorry

lemma box_Int_box:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<inter> box c d =
    box (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  by sorry

lemma cbox_prod: "cbox a b = cbox (fst a) (fst b) \<times> cbox (snd a) (snd b)"
  by sorry

lemma box_prod: "box a b = box (fst a) (fst b) \<times> box (snd a) (snd b)"
  by sorry

lemma rational_boxes:
  fixes x :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<exists>a b. (\<forall>i\<in>Basis. a \<bullet> i \<in> \<rat> \<and> b \<bullet> i \<in> \<rat>) \<and> x \<in> box a b \<and> box a b \<subseteq> ball x e"
  by sorry

lemma open_UNION_box:
  fixes M :: "'a::euclidean_space set"
  assumes "open M"
  defines "a' \<equiv> \<lambda>f :: 'a \<Rightarrow> real \<times> real. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  defines "b' \<equiv> \<lambda>f :: 'a \<Rightarrow> real \<times> real. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  defines "I \<equiv> {f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. box (a' f) (b' f) \<subseteq> M}"
  shows "M = (\<Union>f\<in>I. box (a' f) (b' f))"
  by sorry

corollary open_countable_Union_open_box:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S"
  obtains \<D> where "countable \<D>" "\<D> \<subseteq> Pow S" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = box a b" "\<Union>\<D> = S"
  by sorry

lemma rational_cboxes:
  fixes x :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<exists>a b. (\<forall>i\<in>Basis. a \<bullet> i \<in> \<rat> \<and> b \<bullet> i \<in> \<rat>) \<and> x \<in> cbox a b \<and> cbox a b \<subseteq> ball x e"
  by sorry

lemma open_UNION_cbox:
  fixes M :: "'a::euclidean_space set"
  assumes "open M"
  defines "a' \<equiv> \<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  defines "b' \<equiv> \<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  defines "I \<equiv> {f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. cbox (a' f) (b' f) \<subseteq> M}"
  shows "M = (\<Union>f\<in>I. cbox (a' f) (b' f))"
  by sorry

corollary open_countable_Union_open_cbox:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S"
  obtains \<D> where "countable \<D>" "\<D> \<subseteq> Pow S" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = cbox a b" "\<Union>\<D> = S"
  by sorry

lemma box_eq_empty:
  fixes a :: "'a::euclidean_space"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i < a\<bullet>i))" (is ?th2)
  by sorry

lemma box_ne_empty:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i)"
  and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  by sorry

lemma
  fixes a :: "'a::euclidean_space"
  shows cbox_idem [simp]: "cbox a a = {a}"
    and box_idem [simp]: "box a a = {}"
  by sorry

lemma subset_box_imp:
  fixes a :: "'a::euclidean_space"
  shows "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> cbox a b"
     and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> box a b"
  by sorry

lemma box_subset_cbox:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<subseteq> cbox a b"
  by sorry

lemma subset_box:
  fixes a :: "'a::euclidean_space"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th4)
  by sorry

lemma eq_cbox: "cbox a b = cbox c d \<longleftrightarrow> cbox a b = {} \<and> cbox c d = {} \<or> a = c \<and> b = d"
      (is "?lhs = ?rhs")
  by sorry

lemma eq_cbox_box [simp]: "cbox a b = box c d \<longleftrightarrow> cbox a b = {} \<and> box c d = {}"
  (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma eq_box_cbox [simp]: "box a b = cbox c d \<longleftrightarrow> box a b = {} \<and> cbox c d = {}"
  by sorry

lemma eq_box: "box a b = box c d \<longleftrightarrow> box a b = {} \<and> box c d = {} \<or> a = c \<and> b = d"
  (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma subset_box_complex:
   "cbox a b \<subseteq> cbox c d \<longleftrightarrow>
      (Re a \<le> Re b \<and> Im a \<le> Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
   "cbox a b \<subseteq> box c d \<longleftrightarrow>
      (Re a \<le> Re b \<and> Im a \<le> Im b) \<longrightarrow> Re a > Re c \<and> Im a > Im c \<and> Re b < Re d \<and> Im b < Im d"
   "box a b \<subseteq> cbox c d \<longleftrightarrow>
      (Re a < Re b \<and> Im a < Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
   "box a b \<subseteq> box c d \<longleftrightarrow>
      (Re a < Re b \<and> Im a < Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
  by sorry

lemma in_cbox_complex_iff:
  "x \<in> cbox a b \<longleftrightarrow> Re x \<in> {Re a..Re b} \<and> Im x \<in> {Im a..Im b}"
  by sorry

lemma cbox_complex_of_real: "cbox (complex_of_real x) (complex_of_real y) = complex_of_real ` {x..y}"
  by sorry

lemma box_Complex_eq:
  "box (Complex a c) (Complex b d) = (\<lambda>(x,y). Complex x y) ` (box a b \<times> box c d)"
  by sorry

lemma in_box_complex_iff:
  "x \<in> box a b \<longleftrightarrow> Re x \<in> {Re a<..<Re b} \<and> Im x \<in> {Im a<..<Im b}"
  by sorry

lemma box_complex_of_real [simp]: "box (complex_of_real x) (complex_of_real y) = {}"
  by sorry

lemma cbox_complex_eq: "cbox a b = {x. Re x \<in> {Re a..Re b} \<and> Im x \<in> {Im a..Im b}}"
  by sorry

lemma box_complex_eq: "box a b = {x. Re x \<in> {Re a<..<Re b} \<and> Im x \<in> {Im a<..<Im b}}"
  by sorry

lemma Int_interval:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d =
    cbox (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  by sorry

lemma disjoint_interval:
  fixes a::"'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i < c\<bullet>i \<or> d\<bullet>i < a\<bullet>i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th4)
  by sorry

lemma UN_box_eq_UNIV: "(\<Union>i::nat. box (- (real i *\<^sub>R One)) (real i *\<^sub>R One)) = UNIV"
  by sorry

lemma cbox_shift: "(+) c ` cbox a b = cbox (a + c) (b + c)"
  by sorry

lemma cbox_shift': "(\<lambda>x. x + c) ` cbox a b = cbox (a + c) (b + c)"
  by sorry

lemma cbox_shift'': "(\<lambda>x. x - c) ` cbox a b = cbox (a - c) (b - c)"
  by sorry

lemma image_affinity_cbox: fixes m::real
  fixes a b c :: "'a::euclidean_space"
  shows "(\<lambda>x. m *\<^sub>R x + c) ` cbox a b =
    (if cbox a b = {} then {}
     else (if 0 \<le> m then cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)
     else cbox (m *\<^sub>R b + c) (m *\<^sub>R a + c)))"
  by sorry

lemma image_smult_cbox:"(\<lambda>x. m *\<^sub>R (x::_::euclidean_space)) ` cbox a b =
  (if cbox a b = {} then {} else if 0 \<le> m then cbox (m *\<^sub>R a) (m *\<^sub>R b) else cbox (m *\<^sub>R b) (m *\<^sub>R a))"
  by sorry

lemma swap_continuous:
  assumes "continuous_on (cbox (a,c) (b,d)) (\<lambda>(x,y). f x y)"
    shows "continuous_on (cbox (c,a) (d,b)) (\<lambda>(x, y). f y x)"
  by sorry

lemma open_contains_cbox:
  fixes x :: "'a :: euclidean_space"
  assumes "open A" "x \<in> A"
  obtains a b where "cbox a b \<subseteq> A" "x \<in> box a b" "\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i"
  by sorry

lemma open_contains_box:
  fixes x :: "'a :: euclidean_space"
  assumes "open A" "x \<in> A"
  obtains a b where "box a b \<subseteq> A" "x \<in> box a b" "\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i"
  by sorry

lemma inner_image_box:
  assumes "(i :: 'a :: euclidean_space) \<in> Basis"
  assumes "\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i"
  shows   "(\<lambda>x. x \<bullet> i) ` box a b = {a \<bullet> i<..<b \<bullet> i}"
  by sorry

lemma inner_image_cbox:
  assumes "(i :: 'a :: euclidean_space) \<in> Basis"
  assumes "\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i"
  shows   "(\<lambda>x. x \<bullet> i) ` cbox a b = {a \<bullet> i..b \<bullet> i}"
  by sorry

subsection \<open>General Intervals\<close>

definition\<^marker>\<open>tag important\<close> "is_interval (s::('a::euclidean_space) set) \<longleftrightarrow>
  (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i\<in>Basis. ((a\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> b\<bullet>i) \<or> (b\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> a\<bullet>i))) \<longrightarrow> x \<in> s)"

lemma is_interval_1:
  "is_interval (s::real set) \<longleftrightarrow> (\<forall>a\<in>s. \<forall>b\<in>s. \<forall> x. a \<le> x \<and> x \<le> b \<longrightarrow> x \<in> s)"
  by sorry

lemma is_interval_Int: "is_interval X \<Longrightarrow> is_interval Y \<Longrightarrow> is_interval (X \<inter> Y)"
  by sorry

lemma is_interval_cbox [simp]: "is_interval (cbox a (b::'a::euclidean_space))" (is ?th1)
  and is_interval_box [simp]: "is_interval (box a b)" (is ?th2)
  by sorry

lemma is_interval_empty [iff]: "is_interval {}"
  by sorry

lemma is_interval_univ [iff]: "is_interval UNIV"
  by sorry

lemma mem_is_intervalI:
  assumes "is_interval S"
    and "a \<in> S" "b \<in> S"
    and "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i \<or> b \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i"
  shows "x \<in> S"
  by sorry

lemma interval_subst:
  fixes S::"'a::euclidean_space set"
  assumes "is_interval S"
    and "x \<in> S" "y j \<in> S"
    and "j \<in> Basis"
  shows "(\<Sum>i\<in>Basis. (if i = j then y i \<bullet> i else x \<bullet> i) *\<^sub>R i) \<in> S"
  by sorry

lemma mem_box_componentwiseI:
  fixes S::"'a::euclidean_space set"
  assumes "is_interval S"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i \<in> ((\<lambda>x. x \<bullet> i) ` S)"
  shows "x \<in> S"
  by sorry

lemma cbox01_nonempty [simp]: "cbox 0 One \<noteq> {}"
  by sorry

lemma box01_nonempty [simp]: "box 0 One \<noteq> {}"
  by sorry

lemma empty_as_interval: "{} = cbox One (0::'a::euclidean_space)"
  by sorry

lemma interval_subset_is_interval:
  assumes "is_interval S"
  shows "cbox a b \<subseteq> S \<longleftrightarrow> cbox a b = {} \<or> a \<in> S \<and> b \<in> S" (is "?lhs = ?rhs")
  by sorry

lemma is_real_interval_union:
  "is_interval (X \<union> Y)"
  if X: "is_interval X" and Y: "is_interval Y" and I: "(X \<noteq> {} \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> X \<inter> Y \<noteq> {})"
  for X Y::"real set"
  by sorry

lemma is_interval_translationI:
  assumes "is_interval X"
  shows "is_interval ((+) x ` X)"
  by sorry

lemma is_interval_uminusI:
  assumes "is_interval X"
  shows "is_interval (uminus ` X)"
  by sorry

lemma is_interval_uminus[simp]: "is_interval (uminus ` x) = is_interval x"
  by sorry

lemma is_interval_neg_translationI:
  assumes "is_interval X"
  shows "is_interval ((-) x ` X)"
  by sorry

lemma is_interval_translation[simp]:
  "is_interval ((+) x ` X) = is_interval X"
  by sorry

lemma is_interval_minus_translation[simp]:
  shows "is_interval ((-) x ` X) = is_interval X"
  by sorry

lemma is_interval_minus_translation'[simp]:
  shows "is_interval ((\<lambda>x. x - c) ` X) = is_interval X"
  by sorry

lemma is_interval_cball_1[intro, simp]: "is_interval (cball a b)" for a b::real
  by sorry

lemma is_interval_ball_real: "is_interval (ball a b)" for a b::real
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Bounded Projections\<close>

lemma bounded_inner_imp_bdd_above:
  assumes "bounded s"
    shows "bdd_above ((\<lambda>x. x \<bullet> a) ` s)"
  by sorry

lemma bounded_inner_imp_bdd_below:
  assumes "bounded s"
    shows "bdd_below ((\<lambda>x. x \<bullet> a) ` s)"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Structural rules for pointwise continuity\<close>

lemma continuous_infnorm[continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. infnorm (f x))"
  by sorry

lemma continuous_inner[continuous_intros]:
  assumes "continuous F f"
    and "continuous F g"
  shows "continuous F (\<lambda>x. inner (f x) (g x))"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Structural rules for setwise continuity\<close>

lemma continuous_on_infnorm[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. infnorm (f x))"
  by sorry

lemma continuous_on_inner[continuous_intros]:
  fixes g :: "'a::topological_space \<Rightarrow> 'b::real_inner"
  assumes "continuous_on s f"
    and "continuous_on s g"
  shows "continuous_on s (\<lambda>x. inner (f x) (g x))"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Openness of halfspaces.\<close>

lemma open_halfspace_lt: "open {x. inner a x < b}"
  by sorry

lemma open_halfspace_gt: "open {x. inner a x > b}"
  by sorry

lemma open_halfspace_component_lt: "open {x::'a::euclidean_space. x\<bullet>i < a}"
  by sorry

lemma open_halfspace_component_gt: "open {x::'a::euclidean_space. x\<bullet>i > a}"
  by sorry

lemma eucl_less_eq_halfspaces:
  fixes a :: "'a::euclidean_space"
  shows "{x. x <e a} = (\<Inter>i\<in>Basis. {x. x \<bullet> i < a \<bullet> i})"
        "{x. a <e x} = (\<Inter>i\<in>Basis. {x. a \<bullet> i < x \<bullet> i})"
  by sorry

lemma open_Collect_eucl_less[simp, intro]:
  fixes a :: "'a::euclidean_space"
  shows "open {x. x <e a}" "open {x. a <e x}"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Closure and Interior of halfspaces and hyperplanes\<close>

lemma continuous_at_inner: "continuous (at x) (inner a)"
  by sorry

lemma closed_halfspace_le: "closed {x. inner a x \<le> b}"
  by sorry

lemma closed_halfspace_ge: "closed {x. inner a x \<ge> b}"
  by sorry

lemma closed_hyperplane: "closed {x. inner a x = b}"
  by sorry

lemma closed_halfspace_component_le: "closed {x::'a::euclidean_space. x\<bullet>i \<le> a}"
  by sorry

lemma closed_halfspace_component_ge: "closed {x::'a::euclidean_space. x\<bullet>i \<ge> a}"
  by sorry

lemma closed_interval_left:
  fixes b :: "'a::euclidean_space"
  shows "closed {x::'a. \<forall>i\<in>Basis. x\<bullet>i \<le> b\<bullet>i}"
  by sorry

lemma closed_interval_right:
  fixes a :: "'a::euclidean_space"
  shows "closed {x::'a. \<forall>i\<in>Basis. a\<bullet>i \<le> x\<bullet>i}"
  by sorry

lemma interior_halfspace_le [simp]:
  assumes "a \<noteq> 0"
    shows "interior {x. a \<bullet> x \<le> b} = {x. a \<bullet> x < b}"
  by sorry

lemma interior_halfspace_ge [simp]:
   "a \<noteq> 0 \<Longrightarrow> interior {x. a \<bullet> x \<ge> b} = {x. a \<bullet> x > b}"
  by sorry

lemma closure_halfspace_lt [simp]:
  assumes "a \<noteq> 0"
    shows "closure {x. a \<bullet> x < b} = {x. a \<bullet> x \<le> b}"
  by sorry

lemma closure_halfspace_gt [simp]:
   "a \<noteq> 0 \<Longrightarrow> closure {x. a \<bullet> x > b} = {x. a \<bullet> x \<ge> b}"
  by sorry

lemma interior_hyperplane [simp]:
  assumes "a \<noteq> 0"
    shows "interior {x. a \<bullet> x = b} = {}"
  by sorry

lemma frontier_halfspace_le:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x \<le> b} = {x. a \<bullet> x = b}"
  by sorry

lemma frontier_halfspace_ge:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x \<ge> b} = {x. a \<bullet> x = b}"
  by sorry

lemma frontier_halfspace_lt:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x < b} = {x. a \<bullet> x = b}"
  by sorry

lemma frontier_halfspace_gt:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x > b} = {x. a \<bullet> x = b}"
  by sorry

subsection\<^marker>\<open>tag unimportant\<close>\<open>Some more convenient intermediate-value theorem formulations\<close>

lemma connected_ivt_hyperplane:
  assumes "connected S" and xy: "x \<in> S" "y \<in> S" and b: "inner a x \<le> b" "b \<le> inner a y"
  shows "\<exists>z \<in> S. inner a z = b"
  by sorry

lemma connected_ivt_component:
  fixes x::"'a::euclidean_space"
  shows "connected S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x\<bullet>k \<le> a \<Longrightarrow> a \<le> y\<bullet>k \<Longrightarrow> (\<exists>z\<in>S.  z\<bullet>k = a)"
  by sorry


subsection \<open>Limit Component Bounds\<close>

lemma Lim_component_le:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "(f \<longlongrightarrow> l) net"
    and "\<not> (trivial_limit net)"
    and "eventually (\<lambda>x. f(x)\<bullet>i \<le> b) net"
  shows "l\<bullet>i \<le> b"
  by sorry

lemma Lim_component_ge:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "(f \<longlongrightarrow> l) net"
    and "\<not> (trivial_limit net)"
    and "eventually (\<lambda>x. b \<le> (f x)\<bullet>i) net"
  shows "b \<le> l\<bullet>i"
  by sorry

lemma Lim_component_eq:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes net: "(f \<longlongrightarrow> l) net" "\<not> trivial_limit net"
    and ev:"eventually (\<lambda>x. f(x)\<bullet>i = b) net"
  shows "l\<bullet>i = b"
  by sorry

lemma open_box[intro]: "open (box a b)"
  by sorry

lemma closed_cbox[intro]:
  fixes a b :: "'a::euclidean_space"
  shows "closed (cbox a b)"
  by sorry

lemma interior_cbox [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "interior (cbox a b) = box a b" (is "?L = ?R")
  by sorry

lemma bounded_cbox [simp]:
  fixes a :: "'a::euclidean_space"
  shows "bounded (cbox a b)"
  by sorry

lemma bounded_box [simp]:
  fixes a :: "'a::euclidean_space"
  shows "bounded (box a b)"
  by sorry

lemma not_interval_UNIV [simp]:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> UNIV" "box a b \<noteq> UNIV"
  by sorry

lemma not_interval_UNIV2 [simp]:
  fixes a :: "'a::euclidean_space"
  shows "UNIV \<noteq> cbox a b" "UNIV \<noteq> box a b"
  by sorry

lemma box_midpoint:
  fixes a :: "'a::euclidean_space"
  assumes "box a b \<noteq> {}"
  shows "((1/2) *\<^sub>R (a + b)) \<in> box a b"
  by sorry

lemma open_cbox_convex:
  fixes x :: "'a::euclidean_space"
  assumes x: "x \<in> box a b"
    and y: "y \<in> cbox a b"
    and e: "0 < e" "e \<le> 1"
  shows "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<in> box a b"
  by sorry

lemma closure_cbox [simp]: "closure (cbox a b) = cbox a b"
  by sorry

lemma closure_box [simp]:
  fixes a :: "'a::euclidean_space"
   assumes "box a b \<noteq> {}"
  shows "closure (box a b) = cbox a b"
  by sorry

lemma bounded_subset_box_symmetric:
  fixes S :: "('a::euclidean_space) set"
  assumes "bounded S"
  obtains a where "S \<subseteq> box (-a) a"
  by sorry

lemma bounded_subset_cbox_symmetric:
  fixes S :: "('a::euclidean_space) set"
  assumes "bounded S"
  obtains a where "S \<subseteq> cbox (-a) a"
  by sorry

lemma frontier_cbox:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (cbox a b) = cbox a b - box a b"
  by sorry

lemma frontier_box:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (box a b) = (if box a b = {} then {} else cbox a b - box a b)"
  by sorry

lemma Int_interval_mixed_eq_empty:
  fixes a :: "'a::euclidean_space"
   assumes "box c d \<noteq> {}"
  shows "box a b \<inter> cbox c d = {} \<longleftrightarrow> box a b \<inter> box c d = {}"
  by sorry

subsection \<open>Class Instances\<close>

lemma compact_lemma:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes "bounded (range f)"
  shows "\<forall>d\<subseteq>Basis. \<exists>l::'a. \<exists> r.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) \<bullet> i) (l \<bullet> i) < e) sequentially)"
  by sorry

instance\<^marker>\<open>tag important\<close> euclidean_space \<subseteq> heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "bounded (range f)"
  then obtain l::'a and r where r: "strict_mono r"
    and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e) sequentially"
    using compact_lemma [OF f] by blast
  have "\<forall>\<^sub>F n in sequentially. dist (f (r n)) l < e" if "e > 0" for e::real
  proof -
    from that have "e / real_of_nat DIM('a) > 0" by (simp)
    with l have "eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e / (real_of_nat DIM('a))) sequentially"
      by simp
    moreover
    have "dist (f (r n)) l < e"
      if n: "\<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e / (real_of_nat DIM('a))" for n
    proof -
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i))"
        using L2_set_le_sum [OF zero_le_dist] by (subst euclidean_dist_l2)
      also have "\<dots> < (\<Sum>i\<in>(Basis::'a set). e / (real_of_nat DIM('a)))"
        by (meson eucl.finite_Basis n nonempty_Basis sum_strict_mono)
      finally show ?thesis
        by auto
    qed
    ultimately show ?thesis
      by (rule eventually_mono)
  qed
  then have *: "(f \<circ> r) \<longlonglongrightarrow> l"
    unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    by auto
qed

instance\<^marker>\<open>tag important\<close> euclidean_space \<subseteq> banach ..

instance euclidean_space \<subseteq> second_countable_topology
proof
  define a where "a f = (\<Sum>i\<in>Basis. fst (f i) *\<^sub>R i)" for f :: "'a \<Rightarrow> real \<times> real"
  then have a: "\<And>f. (\<Sum>i\<in>Basis. fst (f i) *\<^sub>R i) = a f"
    by simp
  define b where "b f = (\<Sum>i\<in>Basis. snd (f i) *\<^sub>R i)" for f :: "'a \<Rightarrow> real \<times> real"
  then have b: "\<And>f. (\<Sum>i\<in>Basis. snd (f i) *\<^sub>R i) = b f"
    by simp
  define B where "B = (\<lambda>f. box (a f) (b f)) ` (Basis \<rightarrow>\<^sub>E (\<rat> \<times> \<rat>))"

  have "Ball B open" by (simp add: B_def open_box)
  moreover have "(\<forall>A. open A \<longrightarrow> (\<exists>B'\<subseteq>B. \<Union>B' = A))"
  proof safe
    fix A::"'a set"
    assume "open A"
    show "\<exists>B'\<subseteq>B. \<Union>B' = A"
      using open_UNION_box[OF \<open>open A\<close>]
      by (smt (verit, ccfv_threshold) B_def a b image_iff mem_Collect_eq subsetI)
  qed
  ultimately
  have "topological_basis B"
    unfolding topological_basis_def by blast
  moreover
  have "countable B"
    unfolding B_def
    by (intro countable_image countable_PiE finite_Basis countable_SIGMA countable_rat)
  ultimately show "\<exists>B::'a set set. countable B \<and> open = generate_topology B"
    by (blast intro: topological_basis_imp_subbasis)
qed

instance euclidean_space \<subseteq> polish_space ..


subsection \<open>Compact Boxes\<close>

lemma compact_cbox [simp]:
  fixes a :: "'a::euclidean_space"
  shows "compact (cbox a b)"
  by sorry

proposition is_interval_compact:
   "is_interval S \<and> compact S \<longleftrightarrow> (\<exists>a b. S = cbox a b)"   (is "?lhs = ?rhs")
  by sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Componentwise limits and continuity\<close>

text\<open>But is the premise really necessary? Need to generalise @{thm euclidean_dist_l2}\<close>
lemma Euclidean_dist_upper: "i \<in> Basis \<Longrightarrow> dist (x \<bullet> i) (y \<bullet> i) \<le> dist x y"
  by sorry

text\<open>But is the premise \<^term>\<open>i \<in> Basis\<close> really necessary?\<close>
lemma open_preimage_inner:
  assumes "open S" "i \<in> Basis"
    shows "open {x. x \<bullet> i \<in> S}"
  by sorry

proposition tendsto_componentwise_iff:
  fixes f :: "_ \<Rightarrow> 'b::euclidean_space"
  shows "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>i \<in> Basis. ((\<lambda>x. (f x \<bullet> i)) \<longlongrightarrow> (l \<bullet> i)) F)"
         (is "?lhs = ?rhs")
  by sorry


corollary continuous_componentwise:
   "continuous F f \<longleftrightarrow> (\<forall>i \<in> Basis. continuous F (\<lambda>x. (f x \<bullet> i)))"
  by sorry

corollary continuous_on_componentwise:
  fixes S :: "'a :: t2_space set"
  shows "continuous_on S f \<longleftrightarrow> (\<forall>i \<in> Basis. continuous_on S (\<lambda>x. (f x \<bullet> i)))"
  by sorry

lemma linear_componentwise_iff:
     "linear f' \<longleftrightarrow> (\<forall>i\<in>Basis. linear (\<lambda>x. f' x \<bullet> i))" (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma bounded_linear_componentwise_iff:
     "(bounded_linear f') \<longleftrightarrow> (\<forall>i\<in>Basis. bounded_linear (\<lambda>x. f' x \<bullet> i))"
     (is "?lhs = ?rhs")
  by sorry

subsection\<^marker>\<open>tag unimportant\<close> \<open>Continuous Extension\<close>

definition clamp :: "'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "clamp a b x = (if (\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)
    then (\<Sum>i\<in>Basis. (if x\<bullet>i < a\<bullet>i then a\<bullet>i else if x\<bullet>i \<le> b\<bullet>i then x\<bullet>i else b\<bullet>i) *\<^sub>R i)
    else a)"

lemma clamp_in_interval[simp]:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  shows "clamp a b x \<in> cbox a b"
  by sorry

lemma clamp_cancel_cbox[simp]:
  fixes x a b :: "'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  shows "clamp a b x = x"
  by sorry

lemma clamp_empty_interval:
  assumes "i \<in> Basis" "a \<bullet> i > b \<bullet> i"
  shows "clamp a b = (\<lambda>_. a)"
  by sorry

lemma dist_clamps_le_dist_args:
  fixes x :: "'a::euclidean_space"
  shows "dist (clamp a b y) (clamp a b x) \<le> dist y x"
  by sorry

lemma clamp_continuous_at:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
    and x :: 'a
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous (at x) (\<lambda>x. f (clamp a b x))"
  by sorry

lemma clamp_continuous_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous_on S (\<lambda>x. f (clamp a b x))"
  by sorry

lemma clamp_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes bounded: "bounded (f ` (cbox a b))"
  shows "bounded (range (\<lambda>x. f (clamp a b x)))"
  by sorry


definition ext_cont :: "('a::euclidean_space \<Rightarrow> 'b::metric_space) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b"
  where "ext_cont f a b = (\<lambda>x. f (clamp a b x))"

lemma ext_cont_cancel_cbox[simp]:
  fixes x a b :: "'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  shows "ext_cont f a b x = f x"
  by sorry

lemma continuous_on_ext_cont[continuous_intros]:
  "continuous_on (cbox a b) f \<Longrightarrow> continuous_on S (ext_cont f a b)"
  by sorry


subsection \<open>Separability\<close>

lemma univ_second_countable_sequence:
  obtains B :: "nat \<Rightarrow> 'a::euclidean_space set"
    where "inj B" "\<And>n. open(B n)" "\<And>S. open S \<Longrightarrow> \<exists>k. S = \<Union>{B n |n. n \<in> k}"
  by sorry

proposition separable:
  fixes S :: "'a::{metric_space, second_countable_topology} set"
  obtains T where "countable T" "T \<subseteq> S" "S \<subseteq> closure T"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Diameter\<close>

lemma diameter_cball [simp]:
  fixes a :: "'a::euclidean_space"
  shows "diameter(cball a r) = (if r < 0 then 0 else 2*r)"
  by sorry

lemma diameter_ball [simp]:
  fixes a :: "'a::euclidean_space"
  shows "diameter(ball a r) = (if r < 0 then 0 else 2*r)"
  by sorry

lemma diameter_closed_interval [simp]: "diameter {a..b} = (if b < a then 0 else b-a)"
  by sorry

lemma diameter_open_interval [simp]: "diameter {a<..<b} = (if b < a then 0 else b-a)"
  by sorry

lemma diameter_cbox:
  fixes a b::"'a::euclidean_space"
  shows "(\<forall>i \<in> Basis. a \<bullet> i \<le> b \<bullet> i) \<Longrightarrow> diameter (cbox a b) = dist a b"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close>\<open>Relating linear images to open/closed/interior/closure/connected\<close>

proposition open_surjective_linear_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "open A" "linear f" "surj f"
    shows "open(f ` A)"
  by sorry

corollary open_bijective_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bij f"
    shows "open(f ` A) \<longleftrightarrow> open A"
  by sorry

corollary interior_bijective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bij f"
  shows "interior (f ` S) = f ` interior S" 
  by sorry

lemma interior_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "inj f"
   shows "interior(f ` S) = f ` (interior S)"
  by sorry

lemma interior_surjective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "surj f"
   shows "interior(f ` S) = f ` (interior S)"
  by sorry

lemma interior_negations:
  fixes S :: "'a::euclidean_space set"
  shows "interior(uminus ` S) = image uminus (interior S)"
  by sorry

lemma connected_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "linear f" and "connected s"
  shows "connected (f ` s)"
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>"Isometry" (up to constant bounds) of Injective Linear Map\<close>

proposition injective_imp_isometric:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes s: "closed s" "subspace s"
    and f: "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0"
  shows "\<exists>e>0. \<forall>x\<in>s. norm (f x) \<ge> e * norm x"
  by sorry

proposition closed_injective_image_subspace:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "subspace s" "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0" "closed s"
  shows "closed(f ` s)"
  by sorry
                               

lemma closure_bounded_linear_image_subset:
  assumes f: "bounded_linear f"
  shows "f ` closure S \<subseteq> closure (f ` S)"
  by sorry

lemma closure_linear_image_subset:
  fixes f :: "'m::euclidean_space \<Rightarrow> 'n::real_normed_vector"
  assumes "linear f"
  shows "f ` (closure S) \<subseteq> closure (f ` S)"
  by sorry

lemma closed_injective_linear_image:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    assumes S: "closed S" and f: "linear f" "inj f"
    shows "closed (f ` S)"
  by sorry

lemma closed_injective_linear_image_eq:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    assumes f: "linear f" "inj f"
      shows "(closed(image f s) \<longleftrightarrow> closed s)"
  by sorry

lemma closure_injective_linear_image:
    fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    shows "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> f ` (closure S) = closure (f ` S)"
  by sorry

lemma closure_bounded_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bounded S"
    shows "f ` (closure S) = closure (f ` S)"  (is "?lhs = ?rhs")
  by sorry

lemma closure_scaleR:
  fixes S :: "'a::real_normed_vector set"
  shows "((*\<^sub>R) c) ` (closure S) = closure (((*\<^sub>R) c) ` S)"  (is "?lhs = ?rhs")
  by sorry


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some properties of a canonical subspace\<close>

lemma closed_substandard: "closed {x::'a::euclidean_space. \<forall>i\<in>Basis. P i \<longrightarrow> x\<bullet>i = 0}"
  (is "closed ?A")
  by sorry

lemma closed_subspace:
  fixes S :: "'a::euclidean_space set"
  assumes "subspace S"
  shows "closed S"
  by sorry

lemma complete_subspace: "subspace S \<Longrightarrow> complete S"
  for S :: "'a::euclidean_space set"
  by sorry

lemma closed_span [iff]: "closed (span S)"
  for S :: "'a::euclidean_space set"
  by sorry

lemma dim_closure [simp]: "dim (closure S) = dim S" (is "?dc = ?d")
  for S :: "'a::euclidean_space set"
  by sorry


subsection \<open>Set Distance\<close>

lemma setdist_compact_closed:
  fixes A :: "'a::heine_borel set"
  assumes "compact A" "closed B"
    and "A \<noteq> {}" "B \<noteq> {}"
  shows "\<exists>x \<in> A. \<exists>y \<in> B. dist x y = setdist A B"
  by sorry

lemma setdist_closed_compact:
  fixes S :: "'a::heine_borel set"
  assumes S: "closed S" and T: "compact T"
      and "S \<noteq> {}" "T \<noteq> {}"
    shows "\<exists>x \<in> S. \<exists>y \<in> T. dist x y = setdist S T"
  by sorry

lemma setdist_eq_0_compact_closed:
  assumes S: "compact S" and T: "closed T"
    shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> S \<inter> T \<noteq> {}"
  by sorry

corollary setdist_gt_0_compact_closed:
  assumes S: "compact S" and T: "closed T"
    shows "setdist S T > 0 \<longleftrightarrow> (S \<noteq> {} \<and> T \<noteq> {} \<and> S \<inter> T = {})"
  by sorry

lemma setdist_eq_0_closed_compact:
  assumes S: "closed S" and T: "compact T"
    shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> S \<inter> T \<noteq> {}"
  by sorry

lemma setdist_eq_0_bounded:
  fixes S :: "'a::heine_borel set"
  assumes "bounded S \<or> bounded T"
  shows "setdist S T = 0 \<longleftrightarrow> S = {} \<or> T = {} \<or> closure S \<inter> closure T \<noteq> {}"
  by sorry

lemma setdist_eq_0_sing_1:
  "setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> closure S"
  by sorry

lemma setdist_eq_0_sing_2:
  "setdist S {x} = 0 \<longleftrightarrow> S = {} \<or> x \<in> closure S"
  by sorry

lemma setdist_neq_0_sing_1:
  "\<lbrakk>setdist {x} S = a; a \<noteq> 0\<rbrakk> \<Longrightarrow> S \<noteq> {} \<and> x \<notin> closure S"
  by sorry

lemma setdist_neq_0_sing_2:
  "\<lbrakk>setdist S {x} = a; a \<noteq> 0\<rbrakk> \<Longrightarrow> S \<noteq> {} \<and> x \<notin> closure S"
  by sorry

lemma setdist_sing_in_set:
   "x \<in> S \<Longrightarrow> setdist {x} S = 0"
  by sorry

lemma setdist_eq_0_closed:
   "closed S \<Longrightarrow> (setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> S)"
  by sorry

lemma setdist_eq_0_closedin:
  shows "\<lbrakk>closedin (top_of_set U) S; x \<in> U\<rbrakk>
         \<Longrightarrow> (setdist {x} S = 0 \<longleftrightarrow> S = {} \<or> x \<in> S)"
  by sorry

lemma setdist_gt_0_closedin:
  shows "\<lbrakk>closedin (top_of_set U) S; x \<in> U; S \<noteq> {}; x \<notin> S\<rbrakk>
         \<Longrightarrow> setdist {x} S > 0"
  by sorry

text \<open>A consequence of the results above\<close>
lemma compact_minkowski_sum_cball:
  fixes A :: "'a :: heine_borel set"
  assumes "compact A"
  shows   "compact (\<Union>x\<in>A. cball x r)"
  by sorry

no_notation eucl_less  (infix \<open><e\<close> 50)

end
