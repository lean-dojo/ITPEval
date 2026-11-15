(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light)
                Huge cleanup by LCP
*)

section \<open>Henstock-Kurzweil Gauge Integration in Many Dimensions\<close>

theory Henstock_Kurzweil_Integration
imports
  Lebesgue_Measure Tagged_Division "HOL-Real_Asymp.Real_Asymp"

begin

lemma norm_diff2: "\<lbrakk>y = y1 + y2; x = x1 + x2; e = e1 + e2; norm(y1 - x1) \<le> e1; norm(y2 - x2) \<le> e2\<rbrakk>
  \<Longrightarrow> norm(y-x) \<le> e"
  by sorry

lemma setcomp_dot1: "{z. P (z \<bullet> (i,0))} = {(x,y). P(x \<bullet> i)}"
  by sorry

lemma setcomp_dot2: "{z. P (z \<bullet> (0,i))} = {(x,y). P(y \<bullet> i)}"
  by sorry

lemma Sigma_Int_Paircomp1: "(Sigma A B) \<inter> {(x, y). P x} = Sigma (A \<inter> {x. P x}) B"
  by sorry

lemma Sigma_Int_Paircomp2: "(Sigma A B) \<inter> {(x, y). P y} = Sigma A (\<lambda>z. B z \<inter> {y. P y})"
  by sorry
(* END MOVE *)

subsection \<open>Content (length, area, volume, etc.) of an interval\<close>

abbreviation content :: "'a::euclidean_space set \<Rightarrow> real"
  where "content s \<equiv> measure lborel s"

lemma content_cbox_cases:
  "content (cbox a b) = (if \<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i then prod (\<lambda>i. b\<bullet>i - a\<bullet>i) Basis else 0)"
  by sorry

lemma content_cbox: "\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i \<Longrightarrow> content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  by sorry

lemma content_cbox': "cbox a b \<noteq> {} \<Longrightarrow> content (cbox a b) = (\<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  by sorry

lemma content_cbox_if: "content (cbox a b) = (if cbox a b = {} then 0 else \<Prod>i\<in>Basis. b\<bullet>i - a\<bullet>i)"
  by sorry

lemma content_cbox_cart:
   "cbox a b \<noteq> {} \<Longrightarrow> content(cbox a b) = prod (\<lambda>i. b$i - a$i) UNIV"
  by sorry

lemma content_cbox_if_cart:
   "content(cbox a b) = (if cbox a b = {} then 0 else prod (\<lambda>i. b$i - a$i) UNIV)"
  by sorry

lemma content_division_of:
  assumes "K \<in> \<D>" "\<D> division_of S"
  shows "content K = (\<Prod>i \<in> Basis. interval_upperbound K \<bullet> i - interval_lowerbound K \<bullet> i)"
  by sorry

lemma content_real: "a \<le> b \<Longrightarrow> content {a..b} = b - a"
  by sorry

lemma abs_eq_content: "\<bar>y - x\<bar> = (if x\<le>y then content {x..y} else content {y..x})"
  by sorry

lemma content_singleton: "content {a} = 0"
  by sorry

lemma content_unit[iff]: "content (cbox 0 (One::'a::euclidean_space)) = 1"
  by sorry

lemma content_pos_le [iff]: "0 \<le> content X"
  by sorry

corollary\<^marker>\<open>tag unimportant\<close> content_nonneg [simp]: "\<not> content (cbox a b) < 0"
  by sorry

lemma content_pos_lt: "\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i \<Longrightarrow> 0 < content (cbox a b)"
  by sorry

lemma content_eq_0: "content (cbox a b) = 0 \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i)"
  by sorry

lemma content_eq_0_interior: "content (cbox a b) = 0 \<longleftrightarrow> interior(cbox a b) = {}"
  by sorry

lemma content_pos_lt_eq: "0 < content (cbox a (b::'a::euclidean_space)) \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  by sorry

lemma content_empty [simp]: "content {} = 0"
  by sorry

lemma content_real_if [simp]: "content {a..b} = (if a \<le> b then b - a else 0)"
  by sorry

lemma content_subset: "cbox a b \<subseteq> cbox c d \<Longrightarrow> content (cbox a b) \<le> content (cbox c d)"
  by sorry

lemma content_lt_nz: "0 < content (cbox a b) \<longleftrightarrow> content (cbox a b) \<noteq> 0"
  by sorry

lemma content_Pair: "content (cbox (a,c) (b,d)) = content (cbox a b) * content (cbox c d)"
  by sorry

lemma content_cbox_pair_eq0_D:
   "content (cbox (a,c) (b,d)) = 0 \<Longrightarrow> content (cbox a b) = 0 \<or> content (cbox c d) = 0"
  by sorry

lemma content_cbox_plus:
  fixes x :: "'a::euclidean_space"
  shows "content(cbox x (x + h *\<^sub>R One)) = (if h \<ge> 0 then h ^ DIM('a) else 0)"
  by sorry

lemma content_0_subset: "content(cbox a b) = 0 \<Longrightarrow> s \<subseteq> cbox a b \<Longrightarrow> content s = 0"
  by sorry

lemma content_ball_pos:
  assumes "r > 0"
  shows   "content (ball c r) > 0"
  by sorry

lemma content_cball_pos:
  assumes "r > 0"
  shows   "content (cball c r) > 0"
  by sorry

lemma content_split:
  fixes a :: "'a::euclidean_space"
  assumes "k \<in> Basis"
  shows "content (cbox a b) = content(cbox a b \<inter> {x. x\<bullet>k \<le> c}) + content(cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
  \<comment> \<open>Prove using measure theory\<close>
  by sorry

lemma division_of_content_0:
  assumes "content (cbox a b) = 0" "d division_of (cbox a b)" "K \<in> d"
  shows "content K = 0"
  by sorry

lemma sum_content_null:
  assumes "content (cbox a b) = 0"
    and "p tagged_division_of (cbox a b)"
  shows "(\<Sum>(x,K)\<in>p. content K *\<^sub>R f x) = (0::'a::real_normed_vector)"
  by sorry

global_interpretation sum_content: operative plus 0 content
  rewrites "comm_monoid_set.F plus 0 = sum"
proof -
  interpret operative plus 0 content
    by standard (auto simp: content_split [symmetric] content_eq_0_interior)
  show "operative plus 0 content"
    by standard
  show "comm_monoid_set.F plus 0 = sum"
    by (simp add: sum_def)
qed

lemma additive_content_division: "d division_of (cbox a b) \<Longrightarrow> sum content d = content (cbox a b)"
  by sorry

lemma additive_content_tagged_division:
  "d tagged_division_of (cbox a b) \<Longrightarrow> sum (\<lambda>(x,l). content l) d = content (cbox a b)"
  by sorry

lemma subadditive_content_division:
  assumes "\<D> division_of S" "S \<subseteq> cbox a b"
  shows "sum content \<D> \<le> content(cbox a b)"
  by sorry

lemma content_real_eq_0: "content {a..b::real} = 0 \<longleftrightarrow> a \<ge> b"
  by sorry

lemma property_empty_interval: "\<forall>a b. content (cbox a b) = 0 \<longrightarrow> P (cbox a b) \<Longrightarrow> P {}"
  by sorry

lemma interval_bounds_nz_content [simp]:
  assumes "content (cbox a b) \<noteq> 0"
  shows "interval_upperbound (cbox a b) = b"
    and "interval_lowerbound (cbox a b) = a"
  by sorry

subsection \<open>Gauge integral\<close>

text \<open>Case distinction to define it first on compact intervals first, then use a limit. This is only
much later unified. In Fremlin: Measure Theory, Volume 4I this is generalized using residual sets.\<close>

definition has_integral :: "('n::euclidean_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'b \<Rightarrow> 'n set \<Rightarrow> bool"
  (infixr \<open>has'_integral\<close> 46)
  where "(f has_integral I) s \<longleftrightarrow>
    (if \<exists>a b. s = cbox a b
      then ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R f x) \<longlongrightarrow> I) (division_filter s)
      else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
        (\<exists>z. ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R (if x \<in> s then f x else 0)) \<longlongrightarrow> z) (division_filter (cbox a b)) \<and>
          norm (z - I) < e)))"

lemma has_integral_cbox:
  "(f has_integral I) (cbox a b) \<longleftrightarrow> ((\<lambda>p. \<Sum>(x,k)\<in>p. content k *\<^sub>R f x) \<longlongrightarrow> I) (division_filter (cbox a b))"
  by sorry

lemma has_integral:
  "(f has_integral y) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
      (\<forall>\<D>. \<D> tagged_division_of (cbox a b) \<and> \<gamma> fine \<D> \<longrightarrow>
        norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R f x) - y) < e))"
  by sorry

lemma has_integral_real:
  "(f has_integral y) {a..b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
      (\<forall>\<D>. \<D> tagged_division_of {a..b} \<and> \<gamma> fine \<D> \<longrightarrow>
        norm (sum (\<lambda>(x,k). content(k) *\<^sub>R f x) \<D> - y) < e))"
  by sorry

lemma has_integralD[dest]:
  assumes "(f has_integral y) (cbox a b)"
    and "e > 0"
  obtains \<gamma>
    where "gauge \<gamma>"
      and "\<And>\<D>. \<D> tagged_division_of (cbox a b) \<Longrightarrow> \<gamma> fine \<D> \<Longrightarrow>
        norm ((\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R f x) - y) < e"
  by sorry

lemma has_integral_alt:
  "(f has_integral y) i \<longleftrightarrow>
    (if \<exists>a b. i = cbox a b
     then (f has_integral y) i
     else (\<forall>e>0. \<exists>B>0. \<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f x else 0) has_integral z) (cbox a b) \<and> norm (z - y) < e)))"
  by sorry

lemma has_integral_altD:
  assumes "(f has_integral y) i"
    and "\<not> (\<exists>a b. i = cbox a b)"
    and "e>0"
  obtains B where "B > 0"
    and "\<forall>a b. ball 0 B \<subseteq> cbox a b \<longrightarrow>
      (\<exists>z. ((\<lambda>x. if x \<in> i then f(x) else 0) has_integral z) (cbox a b) \<and> norm(z - y) < e)"
  by sorry

definition integrable_on (infixr \<open>integrable'_on\<close> 46)
  where "f integrable_on i \<longleftrightarrow> (\<exists>y. (f has_integral y) i)"

definition "integral i f = (SOME y. (f has_integral y) i \<or> \<not> f integrable_on i \<and> y=0)"

lemma integrable_integral[intro]: "f integrable_on i \<Longrightarrow> (f has_integral (integral i f)) i"
  by sorry

lemma not_integrable_integral: "\<not> f integrable_on i \<Longrightarrow> integral i f = 0"
  by sorry

lemma has_integral_integrable[dest]: "(f has_integral i) s \<Longrightarrow> f integrable_on s"
  by sorry

lemma has_integral_integral: "f integrable_on s \<longleftrightarrow> (f has_integral (integral s f)) s"
  by sorry

subsection \<open>Basic theorems about integrals\<close>

lemma has_integral_eq_rhs: "(f has_integral j) S \<Longrightarrow> i = j \<Longrightarrow> (f has_integral i) S"
  by sorry

lemma has_integral_unique_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  shows "(f has_integral k1) (cbox a b) \<Longrightarrow> (f has_integral k2) (cbox a b) \<Longrightarrow> k1 = k2"
  by sorry

lemma has_integral_unique:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k1) i" "(f has_integral k2) i"
  shows "k1 = k2"
  by sorry

lemma integral_unique [intro]: "(f has_integral y) k \<Longrightarrow> integral k f = y"
  by sorry

lemma has_integral_iff: "(f has_integral i) S \<longleftrightarrow> (f integrable_on S \<and> integral S f = i)"
  by sorry

lemma eq_integralD: "integral k f = y \<Longrightarrow> (f has_integral y) k \<or> \<not> f integrable_on k \<and> y=0"
  by sorry

lemma has_integral_const [intro]:
  fixes a b :: "'a::euclidean_space"
  shows "((\<lambda>x. c) has_integral (content (cbox a b) *\<^sub>R c)) (cbox a b)"
  by sorry

lemma has_integral_const_real [intro]:
  fixes a b :: real
  shows "((\<lambda>x. c) has_integral (content {a..b} *\<^sub>R c)) {a..b}"
  by sorry

lemma has_integral_integrable_integral: "(f has_integral i) s \<longleftrightarrow> f integrable_on s \<and> integral s f = i"
  by sorry

lemma integral_const [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "integral (cbox a b) (\<lambda>x. c) = content (cbox a b) *\<^sub>R c"
  by sorry

lemma integral_const_real [simp]:
  fixes a b :: real
  shows "integral {a..b} (\<lambda>x. c) = content {a..b} *\<^sub>R c"
  by sorry

lemma has_integral_is_0_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "\<And>x. x \<in> cbox a b \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) (cbox a b)"
  by sorry

lemma has_integral_is_0:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) S"
  by sorry

lemma has_integral_0[simp]: "((\<lambda>x::'n::euclidean_space. 0) has_integral 0) S"
  by sorry

lemma has_integral_0_eq[simp]: "((\<lambda>x. 0) has_integral i) S \<longleftrightarrow> i = 0"
  by sorry

lemma has_integral_linear_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral y) (cbox a b)"
    and h: "bounded_linear h"
  shows "((h \<circ> f) has_integral (h y)) (cbox a b)"
  by sorry

lemma has_integral_linear:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral y) S"
    and h: "bounded_linear h"
  shows "((h \<circ> f) has_integral (h y)) S"
  by sorry

lemma has_integral_of_real:
  "(f has_integral I) A \<Longrightarrow>
     ((\<lambda>x::'a::euclidean_space. of_real (f x) :: 'b :: {real_normed_vector,real_normed_algebra_1}) 
        has_integral of_real I) A"
  by sorry

lemma has_integral_scaleR_left:
  "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x *\<^sub>R c) has_integral (y *\<^sub>R c)) S"
  by sorry

lemma integrable_on_scaleR_left:
  assumes "f integrable_on A"
  shows "(\<lambda>x. f x *\<^sub>R y) integrable_on A"
  by sorry

lemma has_integral_mult_left:
  fixes c :: "_ :: real_normed_algebra"
  shows "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x * c) has_integral (y * c)) S"
  by sorry

lemma integrable_on_mult_left:
  fixes c :: "'a :: real_normed_algebra"
  assumes "f integrable_on A"
  shows   "(\<lambda>x. f x * c) integrable_on A"
  by sorry

lemma has_integral_divide:
  fixes c :: "_ :: real_normed_div_algebra"
  shows "(f has_integral y) S \<Longrightarrow> ((\<lambda>x. f x / c) has_integral (y / c)) S"
  by sorry

lemma integrable_on_divide:
  fixes c :: "'a :: real_normed_div_algebra"
  assumes "f integrable_on A"
  shows   "(\<lambda>x. f x / c) integrable_on A"
  by sorry

text\<open>The case analysis eliminates the condition \<^term>\<open>f integrable_on S\<close> at the cost
     of the type class constraint \<open>division_ring\<close>\<close>
corollary integral_mult_left [simp]:
  fixes c:: "'a::{real_normed_algebra,division_ring}"
  shows "integral S (\<lambda>x. f x * c) = integral S f * c"
  by sorry

corollary integral_mult_right [simp]:
  fixes c:: "'a::{real_normed_field}"
  shows "integral S (\<lambda>x. c * f x) = c * integral S f"
  by sorry

corollary integral_divide [simp]:
  fixes z :: "'a::real_normed_field"
  shows "integral S (\<lambda>x. f x / z) = integral S (\<lambda>x. f x) / z"
  by sorry

lemma has_integral_mult_right:
  fixes c :: "'a :: real_normed_algebra"
  shows "(f has_integral y) A \<Longrightarrow> ((\<lambda>x. c * f x) has_integral (c * y)) A"
  by sorry

lemma integrable_on_mult_right:
  fixes c :: "'a :: real_normed_algebra"
  assumes "f integrable_on A"
  shows   "(\<lambda>x. c * f x) integrable_on A"
  by sorry

lemma has_integral_mult_right_iff:
  fixes c :: "'a :: real_normed_field"
  assumes "c \<noteq> 0"
  shows "((\<lambda>x. c * f x) has_integral y) A \<longleftrightarrow> (f has_integral (y / c)) A"
  by sorry

lemma integrable_on_mult_right_iff [simp]:
  fixes c :: "'a :: real_normed_field"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>x. c * f x) integrable_on A \<longleftrightarrow> f integrable_on A"
  by sorry

lemma integrable_on_mult_left_iff [simp]:
  fixes c :: "'a :: real_normed_field"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>x. f x * c) integrable_on A \<longleftrightarrow> f integrable_on A"
  by sorry

lemma integrable_on_div_iff [simp]:
  fixes c :: "'a :: real_normed_field"
  assumes "c \<noteq> 0"
  shows   "(\<lambda>x. f x / c) integrable_on A \<longleftrightarrow> f integrable_on A"
  by sorry

lemma has_integral_cmul: "(f has_integral k) S \<Longrightarrow> ((\<lambda>x. c *\<^sub>R f x) has_integral (c *\<^sub>R k)) S"
  by sorry

lemma has_integral_cmult_real:
  fixes c :: real
  assumes "c \<noteq> 0 \<Longrightarrow> (f has_integral x) A"
  shows "((\<lambda>x. c * f x) has_integral c * x) A"
  by sorry

lemma has_integral_neg: "(f has_integral k) S \<Longrightarrow> ((\<lambda>x. -(f x)) has_integral -k) S"
  by sorry

lemma has_integral_neg_iff: "((\<lambda>x. - f x) has_integral k) S \<longleftrightarrow> (f has_integral - k) S"
  by sorry

lemma has_integral_add_cbox:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "(f has_integral k) (cbox a b)" "(g has_integral l) (cbox a b)"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) (cbox a b)"
  by sorry

lemma has_integral_add:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes f: "(f has_integral k) S" and g: "(g has_integral l) S"
  shows "((\<lambda>x. f x + g x) has_integral (k + l)) S"
  by sorry

lemma has_integral_diff:
  "(f has_integral k) S \<Longrightarrow> (g has_integral l) S \<Longrightarrow>
    ((\<lambda>x. f x - g x) has_integral (k - l)) S"
  by sorry

lemma integral_0 [simp]:
  "integral S (\<lambda>x::'n::euclidean_space. 0::'m::real_normed_vector) = 0"
  by sorry

lemma integral_add: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow>
    integral S (\<lambda>x. f x + g x) = integral S f + integral S g"
  by sorry

lemma integral_cmul [simp]: "integral S (\<lambda>x. c *\<^sub>R f x) = c *\<^sub>R integral S f"
  by sorry

lemma integral_mult:
  fixes K::real
  shows "f integrable_on X \<Longrightarrow> K * integral X f = integral X (\<lambda>x. K * f x)"
  by sorry

lemma integral_neg [simp]: "integral S (\<lambda>x. - f x) = - integral S f"
  by sorry

lemma integral_diff: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow>
    integral S (\<lambda>x. f x - g x) = integral S f - integral S g"
  by sorry

lemma integrable_0: "(\<lambda>x. 0) integrable_on S"
  by sorry

lemma integrable_add: "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow> (\<lambda>x. f x + g x) integrable_on S"
  by sorry

lemma integrable_cmul: "f integrable_on S \<Longrightarrow> (\<lambda>x. c *\<^sub>R f(x)) integrable_on S"
  by sorry

lemma integrable_on_scaleR_iff [simp]:
  fixes c :: real
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. c *\<^sub>R f x) integrable_on S \<longleftrightarrow> f integrable_on S"
  by sorry

lemma integrable_on_cmult_iff [simp]:
  fixes c :: real
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. c * f x) integrable_on S \<longleftrightarrow> f integrable_on S"
  by sorry

lemma integrable_on_cmult_left:
  assumes "f integrable_on S"
  shows "(\<lambda>x. of_real c * f x) integrable_on S"
  by sorry

lemma integrable_neg: "f integrable_on S \<Longrightarrow> (\<lambda>x. -f(x)) integrable_on S"
  by sorry

lemma integrable_neg_iff: "(\<lambda>x. -f(x)) integrable_on S \<longleftrightarrow> f integrable_on S"
  by sorry

lemma integrable_diff:
  "f integrable_on S \<Longrightarrow> g integrable_on S \<Longrightarrow> (\<lambda>x. f x - g x) integrable_on S"
  by sorry

lemma integrable_linear:
  "f integrable_on S \<Longrightarrow> bounded_linear h \<Longrightarrow> (h \<circ> f) integrable_on S"
  by sorry

lemma integral_linear:
  "f integrable_on S \<Longrightarrow> bounded_linear h \<Longrightarrow> integral S (h \<circ> f) = h (integral S f)"
  by sorry

lemma integrable_on_cnj_iff:
  "(\<lambda>x. cnj (f x)) integrable_on A \<longleftrightarrow> f integrable_on A"
  by sorry

lemma integral_cnj: "cnj (integral A f) = integral A (\<lambda>x. cnj (f x))"
  by sorry

lemma has_integral_cnj: "(cnj \<circ> f has_integral (cnj I)) A  = (f has_integral I) A"
  by sorry

lemma integral_component_eq[simp]:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
  assumes "f integrable_on S"
  shows "integral S (\<lambda>x. f x \<bullet> k) = integral S f \<bullet> k"
  by sorry

lemma integral_eq_iff_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on A"
  shows "integral A f = I \<longleftrightarrow> (\<forall>b\<in>Basis. integral A (\<lambda>x. f x \<bullet> b) = I \<bullet> b)"
  by sorry

lemma has_integral_sum:
  assumes "finite T"
    and "\<And>a. a \<in> T \<Longrightarrow> ((f a) has_integral (i a)) S"
  shows "((\<lambda>x. sum (\<lambda>a. f a x) T) has_integral (sum i T)) S"
  by sorry

lemma integral_sum:
  "\<lbrakk>finite I;  \<And>a. a \<in> I \<Longrightarrow> f a integrable_on S\<rbrakk> \<Longrightarrow>
   integral S (\<lambda>x. \<Sum>a\<in>I. f a x) = (\<Sum>a\<in>I. integral S (f a))"
  by sorry

lemma integrable_sum:
  "\<lbrakk>finite I;  \<And>a. a \<in> I \<Longrightarrow> f a integrable_on S\<rbrakk> \<Longrightarrow> (\<lambda>x. \<Sum>a\<in>I. f a x) integrable_on S"
  by sorry

lemma has_integral_eq:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
    and f: "(f has_integral k) s"
  shows "(g has_integral k) s"
  by sorry

lemma integrable_eq: "\<lbrakk>f integrable_on s; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g integrable_on s"
  by sorry

lemma has_integral_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "(f has_integral i) s = (g has_integral i) s"
  by sorry

lemma integrable_cong:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x"
  shows   "f integrable_on A \<longleftrightarrow> g integrable_on A"
  by sorry

lemma integral_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "integral s f = integral s g"
  by sorry
by (metis (full_types, opaque_lifting) assms has_integral_cong integrable_eq)

lemma integrable_on_cmult_left_iff [simp]:
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. of_real c * f x) integrable_on s \<longleftrightarrow> f integrable_on s"
        (is "?lhs = ?rhs")
  by sorry

lemma integrable_on_cmult_right:
  fixes f :: "_ \<Rightarrow> 'b :: {comm_ring,real_algebra_1,real_normed_vector}"
  assumes "f integrable_on s"
  shows "(\<lambda>x. f x * of_real c) integrable_on s"
  by sorry

lemma integrable_on_cmult_right_iff [simp]:
  fixes f :: "_ \<Rightarrow> 'b :: {comm_ring,real_algebra_1,real_normed_vector}"
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. f x * of_real c) integrable_on s \<longleftrightarrow> f integrable_on s"
  by sorry

lemma integrable_on_cdivide_iff [simp]:
  fixes f :: "_ \<Rightarrow> 'b :: real_normed_field"
  assumes "c \<noteq> 0"
  shows "(\<lambda>x. f x / of_real c) integrable_on s \<longleftrightarrow> f integrable_on s"
  by sorry

lemma has_integral_null [intro]: "content(cbox a b) = 0 \<Longrightarrow> (f has_integral 0) (cbox a b)"
  by sorry

lemma has_integral_null_real [intro]: "content {a..b::real} = 0 \<Longrightarrow> (f has_integral 0) {a..b}"
  by sorry

lemma has_integral_null_eq[simp]: "content (cbox a b) = 0 \<Longrightarrow> (f has_integral i) (cbox a b) \<longleftrightarrow> i = 0"
  by sorry

lemma integral_null [simp]: "content (cbox a b) = 0 \<Longrightarrow> integral (cbox a b) f = 0"
  by sorry

lemma integrable_on_null [intro]: "content (cbox a b) = 0 \<Longrightarrow> f integrable_on (cbox a b)"
  by sorry

lemma has_integral_empty[intro]: "(f has_integral 0) {}"
  by sorry

lemma has_integral_empty_eq[simp]: "(f has_integral i) {} \<longleftrightarrow> i = 0"
  by sorry

lemma integrable_on_empty[intro]: "f integrable_on {}"
  by sorry

lemma integral_empty[simp]: "integral {} f = 0"
  by sorry

lemma has_integral_refl[intro]:
  fixes a :: "'a::euclidean_space"
  shows "(f has_integral 0) (cbox a a)"
    and "(f has_integral 0) {a}"
  by sorry

lemma integrable_on_refl[intro]: "f integrable_on cbox a a"
  by sorry

lemma integral_refl [simp]: "integral (cbox a a) f = 0"
  by sorry

lemma integral_singleton [simp]: "integral {a} f = 0"
  by sorry

lemma integral_blinfun_apply:
  assumes "f integrable_on s"
  shows "integral s (\<lambda>x. blinfun_apply h (f x)) = blinfun_apply h (integral s f)"
  by sorry

lemma blinfun_apply_integral:
  assumes "f integrable_on s"
  shows "blinfun_apply (integral s f) x = integral s (\<lambda>y. blinfun_apply (f y) x)"
  by sorry

lemma has_integral_componentwise_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(f has_integral y) A \<longleftrightarrow> (\<forall>b\<in>Basis. ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A)"
  by sorry

lemma has_integral_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> ((\<lambda>x. f x \<bullet> b) has_integral (y \<bullet> b)) A) \<Longrightarrow> (f has_integral y) A"
  by sorry

lemma integrable_componentwise_iff:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "f integrable_on A \<longleftrightarrow> (\<forall>b\<in>Basis. (\<lambda>x. f x \<bullet> b) integrable_on A)"
  by sorry

lemma integrable_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  shows "(\<And>b. b \<in> Basis \<Longrightarrow> (\<lambda>x. f x \<bullet> b) integrable_on A) \<Longrightarrow> f integrable_on A"
  by sorry

lemma integral_componentwise:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "f integrable_on A"
  shows "integral A f = (\<Sum>b\<in>Basis. integral A (\<lambda>x. (f x \<bullet> b) *\<^sub>R b))"
  by sorry

lemma integrable_component:
  "f integrable_on A \<Longrightarrow> (\<lambda>x. f x \<bullet> (y :: 'b :: euclidean_space)) integrable_on A"
  by sorry

lemma
  assumes "(f has_integral I) A "
  shows has_integral_Re: "((\<lambda>x. Re (f x)) has_integral (Re I)) A"
  and   has_integral_Im: "((\<lambda>x. Im (f x)) has_integral (Im I)) A"
  by sorry


subsection \<open>Cauchy-type criterion for integrability\<close>

proposition integrable_Cauchy:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'a::{real_normed_vector,complete_space}"
  shows "f integrable_on cbox a b \<longleftrightarrow>
        (\<forall>e>0. \<exists>\<gamma>. gauge \<gamma> \<and>
          (\<forall>\<D>1 \<D>2. \<D>1 tagged_division_of (cbox a b) \<and> \<gamma> fine \<D>1 \<and>
            \<D>2 tagged_division_of (cbox a b) \<and> \<gamma> fine \<D>2 \<longrightarrow>
            norm ((\<Sum>(x,K)\<in>\<D>1. content K *\<^sub>R f x) - (\<Sum>(x,K)\<in>\<D>2. content K *\<^sub>R f x)) < e))"
  (is "?l = (\<forall>e>0. \<exists>\<gamma>. ?P e \<gamma>)")
  by sorry


subsection \<open>Additivity of integral on abutting intervals\<close>

lemma tagged_division_split_left_inj_content:
  assumes \<D>: "\<D> tagged_division_of S"
    and "(x1, K1) \<in> \<D>" "(x2, K2) \<in> \<D>" "K1 \<noteq> K2" "K1 \<inter> {x. x\<bullet>k \<le> c} = K2 \<inter> {x. x\<bullet>k \<le> c}" "k \<in> Basis"
  shows "content (K1 \<inter> {x. x\<bullet>k \<le> c}) = 0"
  by sorry

lemma tagged_division_split_right_inj_content:
  assumes \<D>: "\<D> tagged_division_of S"
    and "(x1, K1) \<in> \<D>" "(x2, K2) \<in> \<D>" "K1 \<noteq> K2" "K1 \<inter> {x. x\<bullet>k \<ge> c} = K2 \<inter> {x. x\<bullet>k \<ge> c}" "k \<in> Basis"
  shows "content (K1 \<inter> {x. x\<bullet>k \<ge> c}) = 0"
  by sorry


proposition has_integral_split:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes fi: "(f has_integral i) (cbox a b \<inter> {x. x\<bullet>k \<le> c})"
      and fj: "(f has_integral j) (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"
      and k: "k \<in> Basis"
shows "(f has_integral (i + j)) (cbox a b)"
  by sorry


subsection \<open>A sort of converse, integrability on subintervals\<close>

lemma has_integral_separate_sides:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes f: "(f has_integral i) (cbox a b)"
    and "e > 0"
    and k: "k \<in> Basis"
  obtains d where "gauge d"
    "\<forall>p1 p2. p1 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<le> c}) \<and> d fine p1 \<and>
        p2 tagged_division_of (cbox a b \<inter> {x. x\<bullet>k \<ge> c}) \<and> d fine p2 \<longrightarrow>
        norm ((sum (\<lambda>(x,k). content k *\<^sub>R f x) p1 + sum (\<lambda>(x,k). content k *\<^sub>R f x) p2) - i) < e"
  by sorry

lemma integrable_split [intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::{real_normed_vector,complete_space}"
  assumes f: "f integrable_on cbox a b"
      and k: "k \<in> Basis"
    shows "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<le> c})"   (is ?thesis1)
    and   "f integrable_on (cbox a b \<inter> {x. x\<bullet>k \<ge> c})"   (is ?thesis2)
  by sorry

lemma operative_integralI:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  shows "operative (lift_option (+)) (Some 0)
    (\<lambda>i. if f integrable_on i then Some (integral i f) else None)"
  by sorry

subsection \<open>Bounds on the norm of Riemann sums and the integral itself\<close>

lemma dsum_bound:
  assumes p: "p division_of (cbox a b)"
    and "norm c \<le> e"
  shows "norm (\<Sum>l\<in>p. content l *\<^sub>R c) \<le> e * content(cbox a b)"
  by sorry

lemma rsum_bound:
  assumes p: "p tagged_division_of (cbox a b)"
      and "\<forall>x\<in>cbox a b. norm (f x) \<le> e"
    shows "norm (\<Sum>(x, k)\<in>p. content k *\<^sub>R f x) \<le> e * content (cbox a b)"
  by sorry

lemma rsum_diff_bound:
  assumes "p tagged_division_of (cbox a b)"
    and "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e"
  shows "norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - sum (\<lambda>(x,k). content k *\<^sub>R g x) p) \<le>
         e * content (cbox a b)"
  by sorry

lemma has_integral_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
      and f: "(f has_integral i) (cbox a b)"
      and "\<And>x. x\<in>cbox a b \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content (cbox a b)"
  by sorry

corollary integrable_bound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B"
    and "f integrable_on (cbox a b)"
    and "\<And>x. x\<in>cbox a b \<Longrightarrow> norm (f x) \<le> B"
  shows "norm (integral (cbox a b) f) \<le> B * content (cbox a b)"
  by sorry


subsection \<open>Similar theorems about relationship among components\<close>

lemma rsum_component_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes p: "p tagged_division_of (cbox a b)"
      and "\<And>x. x \<in> cbox a b \<Longrightarrow> (f x)\<bullet>i \<le> (g x)\<bullet>i"
    shows "(\<Sum>(x, K)\<in>p. content K *\<^sub>R f x) \<bullet> i \<le> (\<Sum>(x, K)\<in>p. content K *\<^sub>R g x) \<bullet> i"
  by sorry

lemma has_integral_component_le:
  fixes f g :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes k: "k \<in> Basis"
  assumes "(f has_integral i) S" "(g has_integral j) S"
    and f_le_g: "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "i\<bullet>k \<le> j\<bullet>k"
  by sorry

lemma integral_component_le:
  fixes g f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "f integrable_on S" "g integrable_on S"
    and "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> (g x)\<bullet>k"
  shows "(integral S f)\<bullet>k \<le> (integral S g)\<bullet>k"
  by sorry

lemma has_integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) S"
    and "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> i\<bullet>k"
  by sorry

lemma integral_component_nonneg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and  "\<And>x. x \<in> S \<Longrightarrow> 0 \<le> (f x)\<bullet>k"
  shows "0 \<le> (integral S f)\<bullet>k"
  by sorry

lemma has_integral_component_neg:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "k \<in> Basis"
    and "(f has_integral i) S"
    and "\<And>x. x \<in> S \<Longrightarrow> (f x)\<bullet>k \<le> 0"
  shows "i\<bullet>k \<le> 0"
  by sorry

lemma has_integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> i\<bullet>k"
  by sorry

lemma has_integral_component_ubound:
  fixes f::"'a::euclidean_space => 'b::euclidean_space"
  assumes "(f has_integral i) (cbox a b)"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "i\<bullet>k \<le> B * content (cbox a b)"
  by sorry

lemma integral_component_lbound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content (cbox a b) \<le> (integral(cbox a b) f)\<bullet>k"
  by sorry

lemma integral_component_lbound_real:
  assumes "f integrable_on {a ::real..b}"
    and "\<forall>x\<in>{a..b}. B \<le> f(x)\<bullet>k"
    and "k \<in> Basis"
  shows "B * content {a..b} \<le> (integral {a..b} f)\<bullet>k"
  by sorry

lemma integral_component_ubound:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f integrable_on cbox a b"
    and "\<forall>x\<in>cbox a b. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral (cbox a b) f)\<bullet>k \<le> B * content (cbox a b)"
  by sorry

lemma integral_component_ubound_real:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "f integrable_on {a..b}"
    and "\<forall>x\<in>{a..b}. f x\<bullet>k \<le> B"
    and "k \<in> Basis"
  shows "(integral {a..b} f)\<bullet>k \<le> B * content {a..b}"
  by sorry

subsection \<open>Uniform limit of integrable functions is integrable\<close>

lemma real_arch_invD:
  "0 < (e::real) \<Longrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> 0 < inverse (real n) \<and> inverse (real n) < e)"
  by sorry


lemma integrable_uniform_limit:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::banach"
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>g. (\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e) \<and> g integrable_on cbox a b"
  shows "f integrable_on cbox a b"
  by sorry

lemmas integrable_uniform_limit_real = integrable_uniform_limit [where 'a=real, simplified]


subsection \<open>Negligible sets\<close>

definition "negligible (s:: 'a::euclidean_space set) \<longleftrightarrow>
  (\<forall>a b. ((indicator s :: 'a\<Rightarrow>real) has_integral 0) (cbox a b))"


subsubsection \<open>Negligibility of hyperplane\<close>

lemma content_doublesplit:
  fixes a :: "'a::euclidean_space"
  assumes "0 < e"
    and k: "k \<in> Basis"
  obtains d where "0 < d" and "content (cbox a b \<inter> {x. \<bar>x\<bullet>k - c\<bar> \<le> d}) < e"
  by sorry


proposition negligible_standard_hyperplane[intro]:
  fixes k :: "'a::euclidean_space"
  assumes k: "k \<in> Basis"
  shows "negligible {x. x\<bullet>k = c}"
  by sorry

corollary negligible_standard_hyperplane_cart:
  fixes k :: "'a::finite"
  shows "negligible {x. x$k = (0::real)}"
  by sorry


subsubsection \<open>Hence the main theorem about negligible sets\<close>


lemma has_integral_negligible_cbox:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes negs: "negligible S"
    and 0: "\<And>x. x \<notin> S \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) (cbox a b)"
  by sorry


proposition has_integral_negligible:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes negs: "negligible S"
    and "\<And>x. x \<in> (T - S) \<Longrightarrow> f x = 0"
  shows "(f has_integral 0) T"
  by sorry

lemma
  assumes "negligible S"
  shows integrable_negligible: "f integrable_on S" and integral_negligible: "integral S f = 0"
  by sorry

lemma has_integral_spike:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::real_normed_vector"
  assumes "negligible S"
    and gf: "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and fint: "(f has_integral y) T"
  shows "(g has_integral y) T"
  by sorry

lemma has_integral_spike_eq:
  assumes "negligible S" and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "(f has_integral y) T \<longleftrightarrow> (g has_integral y) T"
  by sorry

lemma integrable_spike:
  assumes "f integrable_on T" "negligible S" "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    shows "g integrable_on T"
  by sorry

lemma integral_spike:
  assumes "negligible S" and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "integral T f = integral T g"
  by sorry


subsection \<open>Some other trivialities about negligible sets\<close>

lemma negligible_subset:
  assumes "negligible S" "T \<subseteq> S"
  shows "negligible T"
  by sorry

lemma negligible_diff[intro?]:
  assumes "negligible S"
  shows "negligible (S - T)"
  by sorry

lemma negligible_Int:
  assumes "negligible S \<or> negligible T"
  shows "negligible (S \<inter> T)"
  by sorry

lemma negligible_Un:
  assumes "negligible S" and T: "negligible T"
  shows "negligible (S \<union> T)"
  by sorry

lemma negligible_Un_eq[simp]: "negligible (S \<union> T) \<longleftrightarrow> negligible S \<and> negligible T"
  by sorry

lemma negligible_sing[intro]: "negligible {a::'a::euclidean_space}"
  by sorry

lemma negligible_insert[simp]: "negligible (insert a S) \<longleftrightarrow> negligible S"
  by sorry

lemma negligible_empty[iff]: "negligible {}"
  by sorry

text\<open>Useful in this form for backchaining\<close>
lemma empty_imp_negligible: "S = {} \<Longrightarrow> negligible S"
  by sorry

lemma negligible_finite[intro]:
  assumes "finite S"
  shows "negligible S"
  by sorry

lemma negligible_Union[intro]:
  assumes "finite \<T>"
    and "\<And>T. T \<in> \<T> \<Longrightarrow> negligible T"
  shows "negligible(\<Union>\<T>)"
  by sorry

lemma negligible: "negligible S \<longleftrightarrow> (\<forall>T. (indicat_real S has_integral 0) T)"
  by sorry

subsection \<open>Finite case of the spike theorem is quite commonly needed\<close>

lemma has_integral_spike_finite:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and "(f has_integral y) T"
  shows "(g has_integral y) T"
  by sorry

lemma has_integral_spike_finite_eq:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
  shows "((f has_integral y) T \<longleftrightarrow> (g has_integral y) T)"
  by sorry

lemma integrable_spike_finite:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> g x = f x"
    and "f integrable_on T"
  shows "g integrable_on T"
  by sorry

lemma integrable_spike_finite_eq:
  assumes "finite S"
    and "\<And>x. x \<in> T - S \<Longrightarrow> f x = g x"
  shows "f integrable_on T \<longleftrightarrow> g integrable_on T"
  by sorry

lemma has_integral_bound_spike_finite:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B" "finite S"
      and f: "(f has_integral i) (cbox a b)"
      and leB: "\<And>x. x \<in> cbox a b - S \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content (cbox a b)"
  by sorry

corollary has_integral_bound_real:
  fixes f :: "real \<Rightarrow> 'b::real_normed_vector"
  assumes "0 \<le> B" "finite S"
      and "(f has_integral i) {a..b}"
      and "\<And>x. x \<in> {a..b} - S \<Longrightarrow> norm (f x) \<le> B"
    shows "norm i \<le> B * content {a..b}"
  by sorry


subsection \<open>In particular, the boundary of an interval is negligible\<close>

lemma negligible_frontier_interval: "negligible(cbox a b - box a b)"
  by sorry

lemma has_integral_spike_interior:
  assumes f: "(f has_integral y) (cbox a b)" and gf: "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
  shows "(g has_integral y) (cbox a b)"
  by sorry
  
lemma has_integral_spike_interior_eq:
  assumes "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
  shows "(f has_integral y) (cbox a b) \<longleftrightarrow> (g has_integral y) (cbox a b)"
  by sorry

lemma integrable_spike_interior:
  assumes "\<And>x. x \<in> box a b \<Longrightarrow> g x = f x"
    and "f integrable_on cbox a b"
  shows "g integrable_on cbox a b"
  by sorry


subsection \<open>Integrability of continuous functions\<close>

lemma operative_approximableI:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
  shows "operative conj True (\<lambda>i. \<exists>g. (\<forall>x\<in>i. norm (f x - g (x::'b)) \<le> e) \<and> g integrable_on i)"
  by sorry

lemma comm_monoid_set_F_and: "comm_monoid_set.F (\<and>) True f s \<longleftrightarrow> (finite s \<longrightarrow> (\<forall>x\<in>s. f x))"
  by sorry

lemma approximable_on_division:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
    and d: "d division_of (cbox a b)"
    and f: "\<forall>i\<in>d. \<exists>g. (\<forall>x\<in>i. norm (f x - g x) \<le> e) \<and> g integrable_on i"
  obtains g where "\<forall>x\<in>cbox a b. norm (f x - g x) \<le> e" "g integrable_on cbox a b"
  by sorry

lemma integrable_continuous:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on (cbox a b) f"
  shows "f integrable_on cbox a b"
  by sorry

lemma integrable_continuous_interval:
  fixes f :: "'b::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "continuous_on {a..b} f"
  shows "f integrable_on {a..b}"
  by sorry

lemmas integrable_continuous_real = integrable_continuous_interval[where 'b=real]

lemma integrable_continuous_closed_segment:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "continuous_on (closed_segment a b) f"
  shows "f integrable_on (closed_segment a b)"
  by sorry


subsection \<open>Specialization of additivity to one dimension\<close>


subsection \<open>A useful lemma allowing us to factor out the content size\<close>

lemma has_integral_factor_content:
  "(f has_integral i) (cbox a b) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of (cbox a b) \<and> d fine p \<longrightarrow>
      norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content (cbox a b)))"
  by sorry

lemma has_integral_factor_content_real:
  "(f has_integral i) {a..b::real} \<longleftrightarrow>
    (\<forall>e>0. \<exists>d. gauge d \<and> (\<forall>p. p tagged_division_of {a..b}  \<and> d fine p \<longrightarrow>
      norm (sum (\<lambda>(x,k). content k *\<^sub>R f x) p - i) \<le> e * content {a..b} ))"
  by sorry


subsection \<open>Fundamental theorem of calculus\<close>

lemma interval_bounds_real:
  fixes q b :: real
  assumes "a \<le> b"
  shows "Sup {a..b} = b"
    and "Inf {a..b} = a"
  by sorry

theorem fundamental_theorem_of_calculus:
  fixes f :: "real \<Rightarrow> 'a::banach"
  assumes "a \<le> b" 
      and vecd: "\<And>x. x \<in> {a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x within {a..b})"
  shows "(f' has_integral (f b - f a)) {a..b}"
  by sorry

lemma has_complex_derivative_imp_has_vector_derivative:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "(f has_field_derivative f') (at (of_real a) within (cbox (of_real x) (of_real y)))"
  shows "((f o of_real) has_vector_derivative f') (at a within {x..y})"
  by sorry

lemma ident_has_integral:
  fixes a::real
  assumes "a \<le> b"
  shows "((\<lambda>x. x) has_integral (b\<^sup>2 - a\<^sup>2)/2) {a..b}"
  by sorry

lemma integral_ident [simp]:
  fixes a::real
  assumes "a \<le> b"
  shows "integral {a..b} (\<lambda>x. x) = (if a \<le> b then (b\<^sup>2 - a\<^sup>2)/2 else 0)"
  by sorry

lemma ident_integrable_on:
  fixes a::real
  shows "(\<lambda>x. x) integrable_on {a..b}"
  by sorry

lemma integral_sin [simp]:
  fixes a::real
  assumes "a \<le> b" shows "integral {a..b} sin = cos a - cos b"
  by sorry

lemma integral_cos [simp]:
  fixes a::real
  assumes "a \<le> b" shows "integral {a..b} cos = sin b - sin a"
  by sorry

lemma integral_exp [simp]:
  fixes a::real
  assumes "a \<le> b" shows "integral {a..b} exp = exp b - exp a"
  by sorry

lemma has_integral_sin_nx: "((\<lambda>x. sin(real_of_int n * x)) has_integral 0) {-pi..pi}"
  by sorry

lemma integral_sin_nx:
   "integral {-pi..pi} (\<lambda>x. sin(x * real_of_int n)) = 0"
  by sorry

lemma has_integral_cos_nx:
  "((\<lambda>x. cos(real_of_int n * x)) has_integral (if n = 0 then 2 * pi else 0)) {-pi..pi}"
  by sorry

lemma integral_cos_nx:
   "integral {-pi..pi} (\<lambda>x. cos(x * real_of_int n)) = (if n = 0 then 2 * pi else 0)"
  by sorry


subsection \<open>Taylor series expansion\<close>

lemma mvt_integral:
  fixes f::"'a::real_normed_vector\<Rightarrow>'b::banach"
  assumes f'[derivative_intros]:
    "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  assumes line_in: "\<And>t. t \<in> {0..1} \<Longrightarrow> x + t *\<^sub>R y \<in> S"
  shows "f (x + y) - f x = integral {0..1} (\<lambda>t. f' (x + t *\<^sub>R y) y)"
  by sorry

lemma (in bounded_bilinear) sum_prod_derivatives_has_vector_derivative:
  assumes "p>0"
  and f0: "Df 0 = f"
  and Df: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Df m has_vector_derivative Df (Suc m) t) (at t within {a..b})"
  and g0: "Dg 0 = g"
  and Dg: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Dg m has_vector_derivative Dg (Suc m) t) (at t within {a..b})"
  and ivl: "a \<le> t" "t \<le> b"
  shows "((\<lambda>t. \<Sum>i<p. (-1)^i *\<^sub>R prod (Df i t) (Dg (p - Suc i) t))
    has_vector_derivative
      prod (f t) (Dg p t) - (-1)^p *\<^sub>R prod (Df p t) (g t))
    (at t within {a..b})"
  by sorry

lemma
  fixes f::"real\<Rightarrow>'a::banach"
  assumes "p>0"
  and f0: "Df 0 = f"
  and Df: "\<And>m t. m < p \<Longrightarrow> a \<le> t \<Longrightarrow> t \<le> b \<Longrightarrow>
    (Df m has_vector_derivative Df (Suc m) t) (at t within {a..b})"
  and ivl: "a \<le> b"
  defines "i \<equiv> \<lambda>x. ((b - x) ^ (p - 1) / fact (p - 1)) *\<^sub>R Df p x"
  shows Taylor_has_integral:
    "(i has_integral f b - (\<Sum>i<p. ((b-a) ^ i / fact i) *\<^sub>R Df i a)) {a..b}"
  and Taylor_integral:
    "f b = (\<Sum>i<p. ((b-a) ^ i / fact i) *\<^sub>R Df i a) + integral {a..b} i"
  and Taylor_integrable:
    "i integrable_on {a..b}"
  by sorry


subsection \<open>Only need trivial subintervals if the interval itself is trivial\<close>

proposition division_of_nontrivial:
  fixes \<D> :: "'a::euclidean_space set set"
  assumes sdiv: "\<D> division_of (cbox a b)"
     and cont0: "content (cbox a b) \<noteq> 0"
  shows "{k. k \<in> \<D> \<and> content k \<noteq> 0} division_of (cbox a b)"
  by sorry

subsection \<open>Integrability on subintervals\<close>

lemma operative_integrableI:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::banach"
  assumes "0 \<le> e"
  shows "operative conj True (\<lambda>i. f integrable_on i)"
  by sorry
