section\<open>The basics of Fourier series\<close>

text\<open>Ported from HOL Light; thanks to Manuel Eberl for help with the real asymp proof methods\<close>

theory "Fourier"
  imports Periodic Square_Integrable "HOL-Real_Asymp.Real_Asymp" Confine Fourier_Aux2
begin

subsection\<open>Orthonormal system of L2 functions and their Fourier coefficients\<close>

definition orthonormal_system :: "'a::euclidean_space set \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where "orthonormal_system S w \<equiv> \<forall>m n. l2product S (w m) (w n) = (if m = n then 1 else 0)"

definition orthonormal_coeff :: "'a::euclidean_space set \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real"
  where "orthonormal_coeff S w f n = l2product S (w n) f"

lemma orthonormal_system_eq: "orthonormal_system S w \<Longrightarrow> l2product S (w m) (w n) = (if m = n then 1 else 0)"
  by sorry

lemma orthonormal_system_l2norm:
   "orthonormal_system S w \<Longrightarrow> l2norm S (w i) = 1"
  by sorry

lemma orthonormal_partial_sum_diff:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S" and "finite I"
  shows "(l2norm S (\<lambda>x. f x - (\<Sum>i\<in>I. a i * w i x)))\<^sup>2 =
        (l2norm S f)\<^sup>2 + (\<Sum>i\<in>I. (a i)\<^sup>2) -  2 * (\<Sum>i\<in>I. a i * orthonormal_coeff S w f i)"
  by sorry

lemma orthonormal_optimal_partial_sum:
  assumes "orthonormal_system S w" "\<And>i. (w i) square_integrable S"
          "f square_integrable S" "finite I"
  shows "l2norm S (\<lambda>x. f x - (\<Sum>i\<in>I. orthonormal_coeff S w f i * w i x))
       \<le> l2norm S (\<lambda>x. f x - (\<Sum>i\<in>I. a i * w i x))"
  by sorry

lemma Bessel_inequality:
  assumes "orthonormal_system S w" "\<And>i. (w i) square_integrable S"
    "f square_integrable S" "finite I"
  shows "(\<Sum>i\<in>I. (orthonormal_coeff S w f i)\<^sup>2) \<le> (l2norm S f)\<^sup>2"
  by sorry

lemma Fourier_series_square_summable:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S"
  shows "summable (confine (\<lambda>i. (orthonormal_coeff S w f i) ^ 2) I)"
  by sorry

lemma orthonormal_Fourier_partial_sum_diff_squared:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S" and "finite I"
  shows "(l2norm S (\<lambda>x. f x -(\<Sum>i\<in>I. orthonormal_coeff S w f i * w i x)))\<^sup>2 =
         (l2norm S f)\<^sup>2 - (\<Sum>i\<in>I. (orthonormal_coeff S w f i)\<^sup>2)"
  by sorry


lemma Fourier_series_l2_summable:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S"
  obtains g where "g square_integrable S"
                  "(\<lambda>n. l2norm S (\<lambda>x. (\<Sum>i\<in>I \<inter> {..n}. orthonormal_coeff S w f i * w i x) - g x))
                   \<longlonglongrightarrow> 0"
  by sorry

lemma Fourier_series_l2_summable_strong:
  assumes os: "orthonormal_system S w" and w: "\<And>i. (w i) square_integrable S"
    and f: "f square_integrable S"
  obtains g where "g square_integrable S"
          "\<And>i. i \<in> I \<Longrightarrow> orthonormal_coeff S w (\<lambda>x. f x - g x) i = 0"
          "(\<lambda>n. l2norm S (\<lambda>x. (\<Sum>i\<in>I \<inter> {..n}. orthonormal_coeff S w f i * w i x) - g x))
           \<longlonglongrightarrow> 0"
  by sorry


subsection\<open>Actual trigonometric orthogonality relations\<close>

lemma integrable_sin_cx:
  "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. sin(x * c))"
  by sorry

lemma integrable_cos_cx:
  "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. cos(x * c))"
  by sorry

lemma integral_cos_Z' [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(n * x)) = (if n = 0 then 2 * pi else 0)"
  by sorry

lemma integral_sin_and_cos:
  fixes m n::int
  shows
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(m * x) * cos(n * x)) = (if \<bar>m\<bar> = \<bar>n\<bar> then if n = 0 then 2 * pi else pi else 0)"
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(m * x) * sin(n * x)) = 0"
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(m * x) * cos(n * x)) = 0"
  "\<lbrakk>m \<ge> 0; n \<ge> 0\<rbrakk> \<Longrightarrow> integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin (m * x) * sin (n * x)) = (if m = n \<and> n \<noteq> 0 then pi else 0)"
  "\<bar>integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin (m * x) * sin (n * x))\<bar> = (if \<bar>m\<bar> = \<bar>n\<bar> \<and> n \<noteq> 0 then pi else 0)"
  by sorry

lemma integral_sin_and_cos_Z [simp]:
  fixes m n::real
  assumes "m \<in> \<int>" "n \<in> \<int>"
  shows
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(m * x) * cos(n * x)) = (if \<bar>m\<bar> = \<bar>n\<bar> then if n = 0 then 2 * pi else pi else 0)"
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(m * x) * sin(n * x)) = 0"
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(m * x) * cos(n * x)) = 0"
  "\<bar>integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin (m * x) * sin (n * x))\<bar> = (if \<bar>m\<bar> = \<bar>n\<bar> \<and> n \<noteq> 0 then pi else 0)"
  by sorry

lemma integral_sin_and_cos_N [simp]:
  fixes m n::real
  assumes "m \<in> \<nat>" "n \<in> \<nat>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin (m * x) * sin (n * x)) = (if m = n \<and> n \<noteq> 0 then pi else 0)"
  by sorry


lemma integrable_sin_and_cos:
  fixes m n::int
  shows "integrable (lebesgue_on {a..b}) (\<lambda>x. cos(x * m) * cos(x * n))"
        "integrable (lebesgue_on {a..b}) (\<lambda>x. cos(x * m) * sin(x * n))"
        "integrable (lebesgue_on {a..b}) (\<lambda>x. sin(x * m) * cos(x * n))"
        "integrable (lebesgue_on {a..b}) (\<lambda>x. sin(x * m) * sin(x * n))"
  by sorry

lemma sqrt_pi_ge1: "sqrt pi \<ge> 1"
  by sorry

definition trigonometric_set :: "nat \<Rightarrow> real \<Rightarrow> real"
  where "trigonometric_set n \<equiv>
    if n = 0 then \<lambda>x. 1 / sqrt(2 * pi)
    else if odd n then \<lambda>x. sin(real(Suc (n div 2)) * x) / sqrt(pi)
    else (\<lambda>x. cos((n div 2) * x) / sqrt pi)"

lemma trigonometric_set:
  "trigonometric_set 0 x = 1 / sqrt(2 * pi)"
  "trigonometric_set (Suc (2 * n)) x = sin(real(Suc n) * x) / sqrt(pi)"
  "trigonometric_set (2 * n + 2) x = cos(real(Suc n) * x) / sqrt(pi)"
  "trigonometric_set (Suc (Suc (2 * n))) x = cos(real(Suc n) * x) / sqrt(pi)"
  by sorry

lemma trigonometric_set_even:
   "trigonometric_set(2*k) = (if k = 0 then (\<lambda>x. 1 / sqrt(2 * pi)) else (\<lambda>x. cos(k * x) / sqrt pi))"
  by sorry

lemma orthonormal_system_trigonometric_set:
    "orthonormal_system {-pi..pi} trigonometric_set"
  by sorry


lemma square_integrable_trigonometric_set:
   "(trigonometric_set i) square_integrable {-pi..pi}"
  by sorry

subsection\<open>Weierstrass for trigonometric polynomials\<close>

lemma Weierstrass_trig_1:
  fixes g :: "real \<Rightarrow> real"
  assumes contf: "continuous_on UNIV g" and periodic: "\<And>x. g(x + 2 * pi) = g x" and 1: "norm z = 1"
  shows "continuous (at z within (sphere 0 1)) (g \<circ> Im \<circ> Ln)"
  by sorry

inductive_set cx_poly :: "(complex \<Rightarrow> real) set" where
    Re: "Re \<in> cx_poly"
  | Im: "Im \<in> cx_poly"
  | const: "(\<lambda>x. c) \<in> cx_poly"
  | add:   "\<lbrakk>f \<in> cx_poly; g \<in> cx_poly\<rbrakk> \<Longrightarrow> (\<lambda>x. f x + g x) \<in> cx_poly"
  | mult:  "\<lbrakk>f \<in> cx_poly; g \<in> cx_poly\<rbrakk> \<Longrightarrow> (\<lambda>x. f x * g x) \<in> cx_poly"

declare cx_poly.intros [intro]


lemma Weierstrass_trig_polynomial:
  assumes contf: "continuous_on {-pi..pi} f" and fpi: "f(-pi) = f pi" and "0 < e"
  obtains n::nat and a b where
    "\<And>x::real. x \<in> {-pi..pi} \<Longrightarrow> \<bar>f x - (\<Sum>k\<le>n. a k * sin (k * x) + b k * cos (k * x))\<bar> < e"
  by sorry


subsection\<open>A bit of extra hacking round so that the ends of a function are OK\<close>

lemma integral_tweak_ends:
  fixes a b :: real
  assumes "a < b" "e > 0"
  obtains f where "continuous_on {a..b} f" "f a = d" "f b = 0" "l2norm {a..b} f < e"
  by sorry


lemma square_integrable_approximate_continuous_ends:
  assumes f: "f square_integrable {a..b}" and "a < b" "0 < e"
  obtains g where "continuous_on {a..b} g" "g b = g a" "g square_integrable {a..b}" "l2norm {a..b} (\<lambda>x. f x - g x) < e"
  by sorry


subsection\<open>Hence the main approximation result\<close>

lemma Weierstrass_l2_trig_polynomial:
  assumes f: "f square_integrable {-pi..pi}" and "0 < e"
  obtains n a b where
   "l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>k\<le>n. a k * sin(real k * x) + b k * cos(real k * x))) < e"
  by sorry


proposition Weierstrass_l2_trigonometric_set:
  assumes f: "f square_integrable {-pi..pi}" and "0 < e"
  obtains n a where "l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>k\<le>n. a k * trigonometric_set k x)) < e"
  by sorry

subsection\<open>Convergence wrt the L2 norm of trigonometric Fourier series\<close>

definition Fourier_coefficient
  where "Fourier_coefficient \<equiv> orthonormal_coeff {-pi..pi} trigonometric_set"

lemma Fourier_series_l2:
  assumes "f square_integrable {-pi..pi}"
  shows "(\<lambda>n. l2norm {-pi..pi} (\<lambda>x. f x - (\<Sum>i\<le>n. Fourier_coefficient f i * trigonometric_set i x)))
         \<longlonglongrightarrow> 0"
  by sorry



subsection\<open>Fourier coefficients go to 0 (weak form of Riemann-Lebesgue)\<close>

lemma trigonometric_set_mul_absolutely_integrable:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. trigonometric_set n x * f x) absolutely_integrable_on {-pi..pi}"
  by sorry


lemma trigonometric_set_mul_integrable:
   "f absolutely_integrable_on {-pi..pi} \<Longrightarrow> integrable (lebesgue_on {-pi..pi}) (\<lambda>x. trigonometric_set n x * f x)"
  by sorry

lemma trigonometric_set_integrable [simp]: "integrable (lebesgue_on {-pi..pi}) (trigonometric_set n)"
  by sorry

lemma absolutely_integrable_sin_product:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. sin(k * x) * f x) absolutely_integrable_on {-pi..pi}"
  by sorry

lemma absolutely_integrable_cos_product:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. cos(k * x) * f x) absolutely_integrable_on {-pi..pi}"
  by sorry

lemma
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows Fourier_products_integrable_cos: "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. cos(k * x) * f x)"
  and   Fourier_products_integrable_sin: "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. sin(k * x) * f x)"
  by sorry


lemma Riemann_lebesgue_square_integrable:
  assumes "orthonormal_system S w" "\<And>i. w i square_integrable S" "f square_integrable S"
  shows "orthonormal_coeff S w f \<longlonglongrightarrow> 0"
  by sorry

proposition Riemann_lebesgue:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "Fourier_coefficient f \<longlonglongrightarrow> 0"
  by sorry


lemma Riemann_lebesgue_sin:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>n. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(real n * x) * f x)) \<longlonglongrightarrow> 0"
  by sorry

lemma Riemann_lebesgue_cos:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>n. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(real n * x) * f x)) \<longlonglongrightarrow> 0"
  by sorry


lemma Riemann_lebesgue_sin_half:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>n. LINT x|lebesgue_on {-pi..pi}. sin ((real n + 1/2) * x) * f x) \<longlonglongrightarrow> 0"
  by sorry


lemma Fourier_sum_limit_pair:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>n. \<Sum>k\<le>2 * n. Fourier_coefficient f k * trigonometric_set k t) \<longlonglongrightarrow> l
     \<longleftrightarrow> (\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) \<longlonglongrightarrow> l"
        (is "?lhs = ?rhs")
  by sorry


subsection\<open>Express Fourier sum in terms of the special expansion at the origin\<close>

lemma Fourier_sum_0:
  "(\<Sum>k \<le> n. Fourier_coefficient f k * trigonometric_set k 0) =
     (\<Sum>k \<le> n div 2. Fourier_coefficient f(2*k) * trigonometric_set (2*k) 0)"
  (is "?lhs = ?rhs")
  by sorry


lemma Fourier_sum_0_explicit:
  "(\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k 0)
    = (Fourier_coefficient f 0 / sqrt 2 + (\<Sum>k = 1..n div 2. Fourier_coefficient f(2*k))) / sqrt pi"
  (is "?lhs = ?rhs")
  by sorry

lemma Fourier_sum_0_integrals:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k 0) =
          (integral\<^sup>L (lebesgue_on {-pi..pi}) f / 2 +
           (\<Sum>k = Suc 0..n div 2. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(k * x) * f x))) / pi"
  by sorry


lemma Fourier_sum_0_integral:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k 0) =
       integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. (1/2 + (\<Sum>k = Suc 0..n div 2. cos(k * x))) * f x) / pi"
  by sorry


subsection\<open>How Fourier coefficients behave under addition etc\<close>

lemma Fourier_coefficient_add:
  assumes "f absolutely_integrable_on {-pi..pi}" "g absolutely_integrable_on {-pi..pi}"
  shows "Fourier_coefficient (\<lambda>x. f x + g x) i =
                Fourier_coefficient f i + Fourier_coefficient g i"
  by sorry

lemma Fourier_coefficient_minus:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "Fourier_coefficient (\<lambda>x. - f x) i = - Fourier_coefficient f i"
  by sorry

lemma Fourier_coefficient_diff:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and g: "g absolutely_integrable_on {-pi..pi}"
  shows "Fourier_coefficient (\<lambda>x. f x - g x) i = Fourier_coefficient f i - Fourier_coefficient g i"
  by sorry

lemma Fourier_coefficient_const:
   "Fourier_coefficient (\<lambda>x. c) i = (if i = 0 then c * sqrt(2 * pi) else 0)"
  by sorry

lemma Fourier_offset_term:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows  "Fourier_coefficient (\<lambda>x. f(x+t)) (2 * n + 2) * trigonometric_set (2 * n + 2) 0
        = Fourier_coefficient f(2 * n+1) * trigonometric_set (2 * n+1) t
        + Fourier_coefficient f(2 * n + 2) * trigonometric_set (2 * n + 2) t"
  by sorry


lemma Fourier_sum_offset:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows  "(\<Sum>k\<le>2*n. Fourier_coefficient f k * trigonometric_set k t) =
          (\<Sum>k\<le>2*n. Fourier_coefficient (\<lambda>x. f(x+t)) k * trigonometric_set k 0)" (is "?lhs = ?rhs")
  by sorry


lemma Fourier_sum_offset_unpaired:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows  "(\<Sum>k\<le>2*n. Fourier_coefficient f k * trigonometric_set k t) =
          (\<Sum>k\<le>n. Fourier_coefficient (\<lambda>x. f(x+t)) (2*k) * trigonometric_set (2*k) 0)"
  (is "?lhs = ?rhs")
  by sorry

subsection\<open>Express partial sums using Dirichlet kernel\<close>

definition Dirichlet_kernel
  where "Dirichlet_kernel \<equiv>
           \<lambda>n x. if x = 0 then real n + 1/2
                          else sin((real n + 1/2) * x) / (2 * sin(x/2))"

lemma Dirichlet_kernel_0 [simp]:
   "\<bar>x\<bar> < 2 * pi \<Longrightarrow> Dirichlet_kernel 0 x = 1/2"
  by sorry

lemma Dirichlet_kernel_minus [simp]: "Dirichlet_kernel n (-x) = Dirichlet_kernel n x"
  by sorry


lemma Dirichlet_kernel_continuous_strong:
   "continuous_on {-(2 * pi)<..<2 * pi} (Dirichlet_kernel n)"
  by sorry

lemma Dirichlet_kernel_continuous: "continuous_on {-pi..pi} (Dirichlet_kernel n)"
  by sorry


lemma absolutely_integrable_mult_Dirichlet_kernel:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. Dirichlet_kernel n x * f x) absolutely_integrable_on {-pi..pi}"
  by sorry


lemma cosine_sum_lemma:
   "(1/2 + (\<Sum>k = Suc 0..n. cos(real k * x))) * sin(x/2) =  sin((real n + 1/2) * x) / 2"
  by sorry


lemma Dirichlet_kernel_cosine_sum:
  assumes "\<bar>x\<bar> < 2 * pi"
  shows "Dirichlet_kernel n x = 1/2 + (\<Sum>k = Suc 0..n. cos(real k * x))"
  by sorry

lemma integrable_Dirichlet_kernel: "integrable (lebesgue_on {-pi..pi}) (Dirichlet_kernel n)"
  by sorry

lemma integral_Dirichlet_kernel [simp]:
  "integral\<^sup>L (lebesgue_on {-pi..pi}) (Dirichlet_kernel n) = pi"
  by sorry

lemma integral_Dirichlet_kernel_half [simp]:
  "integral\<^sup>L (lebesgue_on {0..pi}) (Dirichlet_kernel n) = pi/2"
  by sorry


lemma Fourier_sum_offset_Dirichlet_kernel:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows
   "(\<Sum>k\<le>2*n. Fourier_coefficient f k * trigonometric_set k t) =
            integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * f(x+t)) / pi"
  (is "?lhs = ?rhs")
  by sorry


lemma Fourier_sum_limit_Dirichlet_kernel:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "((\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> l)
     \<longleftrightarrow> (\<lambda>n. LINT x|lebesgue_on {-pi..pi}. Dirichlet_kernel n x * f(x + t)) \<longlonglongrightarrow> pi * l"
    (is "?lhs = ?rhs")
  by sorry

subsection\<open>A directly deduced sufficient condition for convergence at a point\<close>

lemma simple_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and ft: "(\<lambda>x. (f(x+t) - f t) / sin(x/2)) absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
  by sorry


subsection\<open>A more natural sufficient Hoelder condition at a point\<close>

lemma bounded_inverse_sin_half:
  assumes "d > 0"
  obtains B where "B>0" "\<And>x. x \<in> ({-pi..pi} - {-d<..<d}) \<Longrightarrow> \<bar>inverse (sin (x/2))\<bar> \<le> B"
  by sorry

proposition Hoelder_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and "d > 0" "a > 0"
    and ft: "\<And>x. \<bar>x-t\<bar> < d \<Longrightarrow> \<bar>f x - f t\<bar> \<le> M * \<bar>x-t\<bar> powr a"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
  by sorry


text\<open>In particular, a Lipschitz condition at the point\<close>
corollary Lipschitz_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and "d > 0"
    and ft: "\<And>x. \<bar>x-t\<bar> < d \<Longrightarrow> \<bar>f x - f t\<bar> \<le> M * \<bar>x-t\<bar>"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
  by sorry

text\<open>In particular, if left and right derivatives both exist\<close>
proposition bi_differentiable_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and f_lt: "f differentiable at_left t"
    and f_gt: "f differentiable at_right t"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
  by sorry


text\<open>And in particular at points where the function is differentiable\<close>
lemma differentiable_Fourier_convergence_periodic:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and fdif: "f differentiable (at t)"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> f t"
  by sorry

text\<open>Use reflection to halve the region of integration\<close>
lemma absolutely_integrable_mult_Dirichlet_kernel_reflected:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>x. Dirichlet_kernel n x * f(t+x)) absolutely_integrable_on {-pi..pi}"
        "(\<lambda>x. Dirichlet_kernel n x * f(t-x)) absolutely_integrable_on {-pi..pi}"
        "(\<lambda>x. Dirichlet_kernel n x * c) absolutely_integrable_on {-pi..pi}"
  by sorry


lemma absolutely_integrable_mult_Dirichlet_kernel_reflected_part:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Dirichlet_kernel n x * f(t+x)) absolutely_integrable_on {0..d}"
        "(\<lambda>x. Dirichlet_kernel n x * f(t-x)) absolutely_integrable_on {0..d}"
        "(\<lambda>x. Dirichlet_kernel n x * c) absolutely_integrable_on {0..d}"
  by sorry

lemma absolutely_integrable_mult_Dirichlet_kernel_reflected_part2:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Dirichlet_kernel n x * (f(t+x) + f(t-x))) absolutely_integrable_on {0..d}"
        "(\<lambda>x. Dirichlet_kernel n x * ((f(t+x) + f(t-x)) - c)) absolutely_integrable_on {0..d}"
  by sorry

lemma integral_reflect_and_add:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space"
  assumes "integrable (lebesgue_on {-a..a}) f"
  shows "integral\<^sup>L (lebesgue_on {-a..a}) f = integral\<^sup>L (lebesgue_on {0..a})  (\<lambda>x. f x + f(-x))"
  by sorry

lemma Fourier_sum_offset_Dirichlet_kernel_half:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<Sum>k\<le>2*n. Fourier_coefficient f k * trigonometric_set k t) - l
       = (LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * (f(t+x) + f(t-x) - 2*l)) / pi"
  by sorry

lemma Fourier_sum_limit_Dirichlet_kernel_half:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> l
     \<longleftrightarrow> (\<lambda>n. (LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * (f(t+x) + f(t-x) - 2*l))) \<longlonglongrightarrow> 0"
  by sorry


subsection\<open>Localization principle: convergence only depends on values "nearby"\<close>

proposition Riemann_localization_integral:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and g: "g absolutely_integrable_on {-pi..pi}"
    and "d > 0" and d: "\<And>x. \<bar>x\<bar> < d \<Longrightarrow> f x = g x"
  shows "(\<lambda>n. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * f x)
            - integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * g x))
         \<longlonglongrightarrow> 0"  (is "?a \<longlonglongrightarrow> 0")
  by sorry

lemma Riemann_localization_integral_range:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and "0 < d" "d \<le> pi"
  shows "(\<lambda>n. integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. Dirichlet_kernel n x * f x)
            - integral\<^sup>L (lebesgue_on {-d..d}) (\<lambda>x. Dirichlet_kernel n x * f x))
             \<longlonglongrightarrow> 0"
  by sorry

lemma Riemann_localization:
  assumes f: "f absolutely_integrable_on {-pi..pi}" and g: "g absolutely_integrable_on {-pi..pi}"
    and perf: "\<And>x. f(x + 2*pi) = f x"
    and perg: "\<And>x. g(x + 2*pi) = g x"
    and "d > 0" and d: "\<And>x. \<bar>x-t\<bar> < d \<Longrightarrow> f x = g x"
  shows "(\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) \<longlonglongrightarrow> c
     \<longleftrightarrow> (\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient g k * trigonometric_set k t) \<longlonglongrightarrow> c"
  by sorry

subsection\<open>Localize the earlier integral\<close>

lemma Riemann_localization_integral_range_half:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and "0 < d" "d \<le> pi"
  shows "(\<lambda>n. (LINT x|lebesgue_on {0..pi}. Dirichlet_kernel n x * (f x + f(-x)))
            - (LINT x|lebesgue_on {0..d}. Dirichlet_kernel n x * (f x + f(-x)))) \<longlonglongrightarrow> 0"
  by sorry


lemma Fourier_sum_limit_Dirichlet_kernel_part:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
    and d: "0 < d" "d \<le> pi"
  shows "(\<lambda>n. \<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t) \<longlonglongrightarrow> l
     \<longleftrightarrow> (\<lambda>n. (LINT x|lebesgue_on {0..d}. Dirichlet_kernel n x * ((f(t+x) + f(t-x)) - 2*l))) \<longlonglongrightarrow> 0"
  by sorry

subsection\<open>Make a harmless simplifying tweak to the Dirichlet kernel\<close>

lemma inte_Dirichlet_kernel_mul_expand:
  assumes f: "f \<in> borel_measurable (lebesgue_on S)" and S: "S \<in> sets lebesgue"
  shows "(LINT x|lebesgue_on S. Dirichlet_kernel n x * f x
        = LINT x|lebesgue_on S. sin((n+1/2) * x) * f x / (2 * sin(x/2)))
       \<and> (integrable (lebesgue_on S) (\<lambda>x. Dirichlet_kernel n x * f x)
      \<longleftrightarrow> integrable (lebesgue_on S) (\<lambda>x. sin((n+1/2) * x) * f x / (2 * sin(x/2))))"
  by sorry

lemma
  assumes f: "f \<in> borel_measurable (lebesgue_on S)" and S: "S \<in> sets lebesgue"
  shows integral_Dirichlet_kernel_mul_expand:
        "(LINT x|lebesgue_on S. Dirichlet_kernel n x * f x)
       = (LINT x|lebesgue_on S. sin((n+1/2) * x) * f x / (2 * sin(x/2)))" (is "?th1")
  and integrable_Dirichlet_kernel_mul_expand:
       "integrable (lebesgue_on S) (\<lambda>x. Dirichlet_kernel n x * f x)
    \<longleftrightarrow> integrable (lebesgue_on S) (\<lambda>x. sin((n+1/2) * x) * f x / (2 * sin(x/2)))" (is "?th2")
  by sorry


proposition Fourier_sum_limit_sine_part:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
    and d: "0 < d" "d \<le> pi"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> l
     \<longleftrightarrow> (\<lambda>n. LINT x|lebesgue_on {0..d}. sin((n + 1/2) * x) * ((f(t+x) + f(t-x) - 2*l) / x)) \<longlonglongrightarrow> 0"
    (is "?lhs \<longleftrightarrow> ?\<Psi> \<longlonglongrightarrow> 0")
  by sorry


subsection\<open>Dini's test for the convergence of a Fourier series\<close>

proposition Fourier_Dini_test:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
    and int0d: "integrable (lebesgue_on {0..d}) (\<lambda>x. \<bar>f(t+x) + f(t-x) - 2*l\<bar> / x)"
    and "0 < d"
  shows "(\<lambda>n. (\<Sum>k\<le>n. Fourier_coefficient f k * trigonometric_set k t)) \<longlonglongrightarrow> l"
  by sorry


subsection\<open>Cesaro summability of Fourier series using Fejér kernel\<close>

definition Fejer_kernel :: "nat \<Rightarrow> real \<Rightarrow> real"
  where
  "Fejer_kernel \<equiv> \<lambda>n x. if n = 0 then 0 else (\<Sum>r<n. Dirichlet_kernel r x) / n"

lemma Fejer_kernel:
     "Fejer_kernel n x =
        (if n = 0 then 0
         else if x = 0 then n/2
         else sin(n / 2 * x) ^ 2 / (2 * n * sin(x/2) ^ 2))"
  by sorry

lemma Fejer_kernel_0 [simp]: "Fejer_kernel 0 x = 0"  "Fejer_kernel n 0 = n/2"
  by sorry

lemma Fejer_kernel_continuous_strong:
  "continuous_on {-(2 * pi)<..<2 * pi} (Fejer_kernel n)"
  by sorry

lemma Fejer_kernel_continuous:
  "continuous_on {-pi..pi} (Fejer_kernel n)"
  by sorry


lemma absolutely_integrable_mult_Fejer_kernel:
  assumes "f absolutely_integrable_on {-pi..pi}"
  shows "(\<lambda>x. Fejer_kernel n x * f x) absolutely_integrable_on {-pi..pi}"
  by sorry


lemma absolutely_integrable_mult_Fejer_kernel_reflected1:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>x. Fejer_kernel n x * f(t + x)) absolutely_integrable_on {-pi..pi}"
  by sorry

lemma absolutely_integrable_mult_Fejer_kernel_reflected2:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>x. Fejer_kernel n x * f(t - x)) absolutely_integrable_on {-pi..pi}"
  by sorry

lemma absolutely_integrable_mult_Fejer_kernel_reflected3:
  shows "(\<lambda>x. Fejer_kernel n x * c) absolutely_integrable_on {-pi..pi}"
  by sorry


lemma absolutely_integrable_mult_Fejer_kernel_reflected_part1:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * f(t + x)) absolutely_integrable_on {0..d}"
  by sorry

lemma absolutely_integrable_mult_Fejer_kernel_reflected_part2:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * f(t - x)) absolutely_integrable_on {0..d}"
  by sorry

lemma absolutely_integrable_mult_Fejer_kernel_reflected_part3:
  assumes "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * c) absolutely_integrable_on {0..d}"
  by sorry

lemma absolutely_integrable_mult_Fejer_kernel_reflected_part4:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * (f(t + x) + f(t - x))) absolutely_integrable_on {0..d}"
  by sorry

lemma absolutely_integrable_mult_Fejer_kernel_reflected_part5:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "d \<le> pi"
  shows "(\<lambda>x. Fejer_kernel n x * ((f(t + x) + f(t - x)) - c)) absolutely_integrable_on {0..d}"
  by sorry


lemma Fourier_sum_offset_Fejer_kernel_half:
  fixes n::nat
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x" and "n > 0"
  shows "(\<Sum>r<n. \<Sum>k\<le>2*r. Fourier_coefficient f k * trigonometric_set k t) / n - l
       = (LINT x|lebesgue_on {0..pi}. Fejer_kernel n x * (f(t + x) + f(t - x) - 2 * l)) / pi"
  by sorry


lemma Fourier_sum_limit_Fejer_kernel_half:
  fixes n::nat
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. ((\<Sum>r<n. \<Sum>k\<le>2*r. Fourier_coefficient f k * trigonometric_set k t)) / n) \<longlonglongrightarrow> l
         \<longleftrightarrow>
         ((\<lambda>n. integral\<^sup>L (lebesgue_on {0..pi}) (\<lambda>x. Fejer_kernel n x * ((f(t + x) + f(t - x)) - 2*l)))  \<longlonglongrightarrow> 0)"
        (is "?lhs = ?rhs")
  by sorry


lemma has_integral_Fejer_kernel:
  "has_bochner_integral (lebesgue_on {-pi..pi}) (Fejer_kernel n) (if n = 0 then 0 else pi)"
  by sorry

lemma has_integral_Fejer_kernel_half:
  "has_bochner_integral (lebesgue_on {0..pi}) (Fejer_kernel n) (if n = 0 then 0 else pi/2)"
  by sorry

lemma Fejer_kernel_pos_le [simp]: "Fejer_kernel n x \<ge> 0"
  by sorry


theorem Fourier_Fejer_Cesaro_summable:
  assumes f: "f absolutely_integrable_on {-pi..pi}"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
    and fl: "(f \<longlongrightarrow> l) (at t within atMost t)"
    and fr: "(f \<longlongrightarrow> r) (at t within atLeast t)"
  shows "(\<lambda>n. (\<Sum>m<n. \<Sum>k\<le>2*m. Fourier_coefficient f k * trigonometric_set k t) / n) \<longlonglongrightarrow> (l+r) / 2"
  by sorry

corollary Fourier_Fejer_Cesaro_summable_simple:
  assumes f: "continuous_on UNIV f"
    and periodic: "\<And>x. f(x + 2*pi) = f x"
  shows "(\<lambda>n. (\<Sum>m<n. \<Sum>k\<le>2*m. Fourier_coefficient f k * trigonometric_set k x) / n) \<longlonglongrightarrow> f x"
  by sorry

end


