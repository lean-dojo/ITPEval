(*  
  File:       Bernoulli.thy
  Author:     Lukas Bulwahn <lukas.bulwahn-at-gmail.com> 
  Author:     Manuel Eberl <manuel@pruvisto.org> 
*)
section \<open>Bernoulli numbers\<close>

theory Bernoulli
imports Complex_Main
begin

subsection \<open>Preliminaries\<close>
  
lemma power_numeral_reduce: "a ^ numeral n = a * a ^ pred_numeral n"
  by sorry

lemma fact_diff_Suc: "n < Suc m \<Longrightarrow> fact (Suc m - n) = of_nat (Suc m - n) * fact (m - n)"
  by sorry

lemma of_nat_binomial_Suc:
  assumes "k \<le> n"
  shows   "(of_nat (Suc n choose k) :: 'a :: field_char_0) = 
             of_nat (Suc n) / of_nat (Suc n - k) * of_nat (n choose k)"
  by sorry

lemma integrals_eq:
  assumes "f 0 = g 0"
  assumes "\<And> x. ((\<lambda>x. f x - g x) has_real_derivative 0) (at x)"
  shows "f x = g x"
  by sorry

lemma sum_diff: "((\<Sum>i\<le>n::nat. f (i + 1) - f i)::'a::field) = f (n + 1) - f 0"
  by sorry
    
lemma Rats_sum: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<rat>) \<Longrightarrow> sum f A \<in> \<rat>"
  by sorry


subsection \<open>Bernoulli Numbers and Bernoulli Polynomials\<close>

declare sum.cong [fundef_cong]

fun bernoulli :: "nat \<Rightarrow> 'a :: field_char_0"
where
  "bernoulli 0 = 1"
| "bernoulli (Suc n) =  (-1 / (of_nat n + 2)) * (\<Sum>k \<le> n. (of_nat (n + 2 choose k) * bernoulli k))"
  
declare bernoulli.simps[simp del]
  
lemmas bernoulli_0 [simp] = bernoulli.simps(1)
lemmas bernoulli_Suc = bernoulli.simps(2)
lemma bernoulli_1 [simp]: "bernoulli 1 = -1/2" by (simp add: bernoulli_Suc)
lemma bernoulli_Suc_0 [simp]: "bernoulli (Suc 0) = -1/2" by (simp add: bernoulli_Suc)

lemma of_rat_bernoulli: "of_rat (bernoulli n) = bernoulli n"
  by sorry

(* TODO: Move *)
lemma of_real_of_rat: "of_real (of_rat x) = (of_rat x :: 'a :: real_field)"
  by sorry

lemma of_real_bernoulli: "of_real (bernoulli n) = (bernoulli n :: 'a :: real_field)"
  by sorry

    
text \<open>
  The ``normal'' Bernoulli numbers are the negative Bernoulli numbers $B_n^{-}$ we just defined
  (so called because $B_1^{-} = -\frac{1}{2}$). There is also another convention, the 
  positive Bernoulli numbers $B_n^{+}$, which differ from the negative ones only in that 
  $B_1^{+} = \frac{1}{2}$. Both conventions have their justification, since a number of theorems 
  are easier to state with one than the other.
\<close>
definition bernoulli' :: "nat \<Rightarrow> 'a :: field_char_0" where
  "bernoulli' n = (if n = 1 then 1/2 else bernoulli n)"
  
lemma bernoulli'_0 [simp]: "bernoulli' 0 = 1" by (simp add: bernoulli'_def)
    
lemma bernoulli'_1 [simp]: "bernoulli' (Suc 0) = 1/2"
  by sorry

lemma bernoulli_conv_bernoulli': "n \<noteq> 1 \<Longrightarrow> bernoulli n = bernoulli' n"
  by sorry
    
lemma bernoulli'_conv_bernoulli: "n \<noteq> 1 \<Longrightarrow> bernoulli' n = bernoulli n"
  by sorry
    
lemma bernoulli_conv_bernoulli'_if: 
    "n \<noteq> 1 \<Longrightarrow> bernoulli n = (if n = 1 then -1/2 else bernoulli' n)"
  by sorry

lemma of_rat_bernoulli': "of_rat (bernoulli' n) = bernoulli' n"
  by sorry

lemma of_real_bernoulli': "of_real (bernoulli' n) = (bernoulli' n :: 'a :: real_field)"
  by sorry

lemma bernoulli_in_Rats: "bernoulli n \<in> \<rat>"
  by sorry

lemma bernoulli'_in_Rats: "bernoulli' n \<in> \<rat>"
  by sorry

definition bernpoly :: "nat \<Rightarrow> 'a \<Rightarrow> 'a :: real_algebra_1" where
  "bernpoly n = (\<lambda>x. \<Sum>k \<le> n. of_nat (n choose k) * of_real (bernoulli k) * x ^ (n - k))"
  
lemma bernpoly_altdef:
  "bernpoly n = (\<lambda>x. \<Sum>k\<le>n. of_nat (n choose k) * of_real (bernoulli (n - k)) * x ^ k)"
  by sorry

lemma bernoulli_Suc': 
  "bernoulli (Suc n) = -1/(of_nat n + 2) * (\<Sum>k\<le>n. of_nat (n + 2 choose (k + 2)) * bernoulli (n - k))" 
  by sorry
  

subsection \<open>Basic Observations on Bernoulli Polynomials\<close>

lemma bernpoly_0 [simp]: "bernpoly n 0 = of_real (bernoulli n)"
  by sorry

lemma continuous_on_bernpoly [continuous_intros]: 
  "continuous_on A (bernpoly n :: 'a \<Rightarrow> 'a :: real_normed_algebra_1)"
  by sorry

lemma isCont_bernpoly [continuous_intros]: 
  "isCont (bernpoly n :: 'a \<Rightarrow> 'a :: real_normed_algebra_1) x"
  by sorry

lemma has_field_derivative_bernpoly:
  "(bernpoly (Suc n) has_field_derivative 
     (of_nat (n + 1) * bernpoly n x :: 'a :: real_normed_field)) (at x)"
  by sorry
  
lemmas has_field_derivative_bernpoly' [derivative_intros] =
  DERIV_chain'[OF _ has_field_derivative_bernpoly]    

lemma sum_binomial_times_bernoulli:
  "(\<Sum>k\<le>n. of_nat ((Suc n) choose k) * bernoulli k) = (if n = 0 then 1 else 0)"
  by sorry
  
lemma sum_binomial_times_bernoulli':
  "(\<Sum>k<n. of_nat (n choose k) * bernoulli k :: 'a :: field_char_0) = (if n = 1 then 1 else 0)"
  by sorry
  
lemma binomial_unroll:
  "n > 0 \<Longrightarrow> (n choose k) = (if k = 0 then 1 else ((n - 1) choose (k - 1)) + ((n - 1) choose k))"
  by sorry

lemma sum_unroll:
  "(\<Sum>k\<le>n::nat. f k) = (if n = 0 then f 0 else f n + (\<Sum>k\<le>n - 1. f k))"
  by sorry

lemma bernoulli_unroll:
  "n > 0 \<Longrightarrow> bernoulli n = - 1 / (of_nat n + 1) * (\<Sum>k\<le>n - 1. of_nat (n + 1 choose k) * bernoulli k)"
  by sorry

lemmas bernoulli_unroll_all = binomial_unroll bernoulli_unroll sum_unroll bernpoly_def

lemma bernpoly_1_1: "bernpoly 1 1 = of_real (1/2)"
  by sorry


subsection \<open>Sum of Powers with Bernoulli Polynomials\<close>

(* TODO: Generalisation not possible here because mean-value theorem 
   is only available for reals *)
lemma diff_bernpoly:
  fixes x :: real
  shows "bernpoly n (x + 1) - bernpoly n x = of_nat n * x ^ (n - 1)"
  by sorry

lemma bernpoly_of_real: "bernpoly n (of_real x) = of_real (bernpoly n x)"
  by sorry
  
lemma bernpoly_1:
  assumes "n \<noteq> 1"
  shows   "bernpoly n 1 = of_real (bernoulli n)"
  by sorry
  
lemma bernpoly_1': "bernpoly n 1 = of_real (bernoulli' n)"
  by sorry

theorem sum_of_powers: 
  "(\<Sum>k\<le>n::nat. (real k) ^ m) = (bernpoly (Suc m) (n + 1) - bernpoly (Suc m) 0) / (m + 1)"
  by sorry
  
lemma sum_of_powers_nat_aux: 
  assumes "real a = b / c" "real b' = b" "real c' = c"
  shows   "a = b' div c'"
  by sorry


subsection \<open>Instances for Square And Cubic Numbers\<close>

theorem sum_of_squares: "real (\<Sum>k\<le>n::nat. k ^ 2) = real (2 * n ^ 3 + 3 * n ^ 2 + n) / 6"
  by sorry

corollary sum_of_squares_nat: "(\<Sum>k\<le>n::nat. k ^ 2) = (2 * n ^ 3 + 3 * n ^ 2 + n) div 6"
  by sorry

theorem sum_of_cubes: "real (\<Sum>k\<le>n::nat. k ^ 3) = real (n ^ 2 + n) ^ 2 / 4"
  by sorry
                       
corollary sum_of_cubes_nat: "(\<Sum>k\<le>n::nat. k ^ 3) = (n ^ 2 + n) ^ 2 div 4"
  by sorry

end
