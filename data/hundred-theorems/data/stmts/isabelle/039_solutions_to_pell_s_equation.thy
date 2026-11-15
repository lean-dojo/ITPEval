(*
  File:     Pell.thy
  Author:   Manuel Eberl, TU München

  Basic facts about the solutions of Pell's equation
*)
section \<open>Pell's equation\<close>
theory Pell
imports
  Complex_Main
  "HOL-Computational_Algebra.Computational_Algebra"
begin

text \<open>
  Pell's equation has the general form $x^2 = 1 + D y^2$ where \<open>D \<in> \<nat>\<close> is a parameter
  and \<open>x\<close>, \<open>y\<close> are \<open>\<int>\<close>-valued variables. As we will see, that case where \<open>D\<close> is a
  perfect square is trivial and therefore uninteresting; we will therefore assume that \<open>D\<close> is
  not a perfect square for the most part.

  Furthermore, it is obvious that the solutions to Pell's equation are symmetric around the
  origin in the sense that \<open>(x, y)\<close> is a solution iff \<open>(\<plusminus>x, \<plusminus>y)\<close> is a solution. We will
  therefore mostly look at solutions \<open>(x, y)\<close> where both \<open>x\<close> and \<open>y\<close> are non-negative, since
  the remaining solutions are a trivial consequence of these.

  Information on the material treated in this formalisation can be found in many textbooks and
   lecture notes, e.\,g.\ \<^cite>\<open>"jacobson2008solving" and "auckland_pell"\<close>.
\<close>

subsection \<open>Preliminary facts\<close>

lemma gcd_int_nonpos_iff [simp]: "gcd x (y :: int) \<le> 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by sorry

lemma minus_in_Ints_iff [simp]:
  "-x \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  by sorry

text \<open>
  A (positive) square root of a natural number is either a natural number or irrational.
\<close>
lemma nonneg_sqrt_nat_or_irrat:
  assumes "x ^ 2 = real a" and "x \<ge> 0"
  shows   "x \<in> \<nat> \<or> x \<notin> \<rat>"
  by sorry

text \<open>
  A square root of a natural number is either an integer or irrational.
\<close>
corollary sqrt_nat_or_irrat:
  assumes "x ^ 2 = real a"
  shows   "x \<in> \<int> \<or> x \<notin> \<rat>"
  by sorry

corollary sqrt_nat_or_irrat':
  "sqrt (real a) \<in> \<nat> \<or> sqrt (real a) \<notin> \<rat>"
  by sorry

text \<open>
  The square root of a natural number \<open>n\<close> is again a natural number iff \<open>n is a perfect square.\<close>
\<close>
corollary sqrt_nat_iff_is_square:
  "sqrt (real n) \<in> \<nat> \<longleftrightarrow> is_square n"
  by sorry

corollary irrat_sqrt_nonsquare: "\<not>is_square n \<Longrightarrow> sqrt (real n) \<notin> \<rat>"
  by sorry


subsection \<open>The case of a perfect square\<close>

text \<open>
  As we have noted, the case where \<open>D\<close> is a perfect square is trivial: In fact, we will
  show that the only solutions in this case are the trivial solutions \<open>(x, y) = (\<plusminus>1, 0)\<close> if
  \<open>D\<close> is a non-zero perfect square, or \<open>(\<plusminus>1, y)\<close> for arbitrary \<open>y \<in> \<int>\<close> if \<open>D = 0\<close>.
\<close>
context
  fixes D :: nat
  assumes square_D: "is_square D"
begin

lemma pell_square_solution_nat_aux:
  fixes x y :: nat
  assumes "D > 0" and "x ^ 2 = 1 + D * y ^ 2"
  shows "(x, y) = (1, 0)"
  by sorry

lemma pell_square_solution_int_aux:
  fixes x y :: int
  assumes "D > 0" and "x ^ 2 = 1 + D * y ^ 2"
  shows "x \<in> {-1, 1} \<and> y = 0"
  by sorry

lemma pell_square_solution_nat_iff:
  fixes x y :: nat
  shows "x ^ 2 = 1 + D * y ^ 2  \<longleftrightarrow>  x = 1 \<and> (D = 0 \<or> y = 0)"
  by sorry

lemma pell_square_solution_int_iff:
  fixes x y :: int
  shows "x ^ 2 = 1 + D * y ^ 2  \<longleftrightarrow>  x \<in> {-1, 1} \<and> (D = 0 \<or> y = 0)"
  by sorry

end


subsection \<open>Existence of a non-trivial solution\<close>

text \<open>
  Let us now turn to the case where \<open>D\<close> is not a perfect square.

  We first show that Pell's equation always has at least one non-trivial solution (apart
  from the trivial solution \<open>(1, 0)\<close>). For this, we first need a lemma about the existence
  of rational approximations of real numbers.

  The following lemma states that for any positive integer \<open>s\<close> and real number \<open>x\<close>, we can find a
  rational approximation \<open>t / u\<close> to \<open>x\<close> with an error of most \<open>1 / (u * s)\<close> where the denominator
  \<open>u\<close> is at most \<open>s\<close>.
\<close>
lemma pell_approximation_lemma:
  fixes s :: nat and x :: real
  assumes s: "s > 0"
  shows "\<exists>u::nat. \<exists>t::int. u > 0 \<and> coprime u t \<and> 1 / s \<in> {\<bar>t - u * x\<bar><..1 / u}"
  by sorry

text \<open>
  As a simple corollary of this, we can show that for irrational \<open>x\<close>, there is an infinite
  number of rational approximations \<open>t / u\<close> to \<open>x\<close> whose error is less that \<open>1 / u\<^sup>2\<close>.
\<close>
corollary pell_approximation_corollary:
  fixes x :: real
  assumes "x \<notin> \<rat>"
  shows "infinite {(t :: int, u :: nat). u > 0 \<and> coprime u t \<and> \<bar>t - u * x\<bar> < 1 / u}"
    (is "infinite ?A")
  by sorry


locale pell =
  fixes D :: nat
  assumes nonsquare_D: "\<not>is_square D"
begin

lemma D_gt_1: "D > 1"
  by sorry

lemma D_pos: "D > 0"
  by sorry

text \<open>
  With the above corollary, we can show the existence of a non-trivial solution. We restrict our
  attention to solutions \<open>(x, y)\<close> where both \<open>x\<close> and \<open>y\<close> are non-negative.
\<close>
theorem pell_solution_exists: "\<exists>(x::nat) (y::nat). y \<noteq> 0 \<and> x\<^sup>2 = 1 + D * y\<^sup>2"
  by sorry


subsection \<open>Definition of solutions\<close>

text \<open>
  We define some abbreviations for the concepts of a solution and a non-trivial solution.
\<close>
definition solution :: "('a \<times> 'a :: comm_semiring_1) \<Rightarrow> bool" where
  "solution = (\<lambda>(a, b). a\<^sup>2 = 1 + of_nat D * b\<^sup>2)"

definition nontriv_solution :: "('a \<times> 'a :: comm_semiring_1) \<Rightarrow> bool" where
  "nontriv_solution = (\<lambda>(a, b). (a, b) \<noteq> (1, 0) \<and> a\<^sup>2 = 1 + of_nat D * b\<^sup>2)"

lemma nontriv_solution_altdef: "nontriv_solution z \<longleftrightarrow> solution z \<and> z \<noteq> (1, 0)"
  by sorry

lemma solution_trivial_nat [simp, intro]: "solution (Suc 0, 0)"
  by sorry

lemma solution_trivial [simp, intro]: "solution (1, 0)"
  by sorry

lemma solution_uminus_left [simp]: "solution (-x, y :: 'a :: comm_ring_1) \<longleftrightarrow> solution (x, y)"
  by sorry

lemma solution_uminus_right [simp]: "solution (x, -y :: 'a :: comm_ring_1) \<longleftrightarrow> solution (x, y)"
  by sorry

lemma solution_0_snd_nat_iff [simp]: "solution (a :: nat, 0) \<longleftrightarrow> a = 1"
  by sorry

lemma solution_0_snd_iff [simp]: "solution (a :: 'a :: idom, 0) \<longleftrightarrow> a \<in> {1, -1}"
  by sorry

lemma no_solution_0_fst_nat [simp]: "\<not>solution (0, b :: nat)"
  by sorry

lemma no_solution_0_fst_int [simp]: "\<not>solution (0, b :: int)"
  by sorry

lemma solution_of_nat_of_nat [simp]:
  "solution (of_nat a, of_nat b :: 'a :: {comm_ring_1, ring_char_0}) \<longleftrightarrow> solution (a, b)"
  by sorry

lemma solution_of_nat_of_nat' [simp]:
  "solution (case z of (a, b) \<Rightarrow> (of_nat a, of_nat b :: 'a :: {comm_ring_1, ring_char_0})) \<longleftrightarrow>
     solution z"
  by sorry

lemma solution_nat_abs_nat_abs [simp]:
  "solution (nat \<bar>x\<bar>, nat \<bar>y\<bar>) \<longleftrightarrow> solution (x, y)"
  by sorry

lemma nontriv_solution_of_nat_of_nat [simp]:
  "nontriv_solution (of_nat a, of_nat b :: 'a :: {comm_ring_1, ring_char_0}) \<longleftrightarrow> nontriv_solution (a, b)"
  by sorry

lemma nontriv_solution_of_nat_of_nat' [simp]:
  "nontriv_solution (case z of (a, b) \<Rightarrow> (of_nat a, of_nat b :: 'a :: {comm_ring_1, ring_char_0})) \<longleftrightarrow>
     nontriv_solution z"
  by sorry

lemma nontriv_solution_imp_solution [dest]: "nontriv_solution z \<Longrightarrow> solution z"
  by sorry


subsection \<open>The Pell valuation function\<close>

text \<open>
  Solutions \<open>(x,y)\<close> have an interesting correspondence to the ring $\mathbb{Z}[\sqrt{D}]$ via
  the map $(x,y) \mapsto x + y \sqrt{D}$. We call this map the \<^emph>\<open>Pell valuation function\<close>.
  It is obvious that this map is injective, since $\sqrt{D}$ is irrational.
\<close>
definition pell_valuation :: "int \<times> int \<Rightarrow> real" where
  "pell_valuation = (\<lambda>(a,b). a + b * sqrt D)"

lemma pell_valuation_nonneg [simp]: "fst z \<ge> 0 \<Longrightarrow> snd z \<ge> 0 \<Longrightarrow> pell_valuation z \<ge> 0"
  by sorry

lemma pell_valuation_uminus_uminus [simp]: "pell_valuation (-x, -y) = -pell_valuation (x, y)"
  by sorry

lemma pell_valuation_eq_iff [simp]:
  "pell_valuation z1 = pell_valuation z2 \<longleftrightarrow> z1 = z2"
  by sorry


subsection \<open>Linear ordering of solutions\<close>

text \<open>
  Next, we show that solutions are linearly ordered w.\,r.\,t.\ the pointwise order on products.
  This means thatfor two different solutions \<open>(a, b)\<close> and \<open>(x, y)\<close>, we always either have
  \<open>a < x\<close> and \<open>b < y\<close> or \<open>a > x\<close> and \<open>b > y\<close>.
\<close>

lemma solutions_linorder:
  fixes a b x y :: nat
  assumes "solution (a, b)" "solution (x, y)"
  shows   "a \<le> x \<and> b \<le> y \<or> a \<ge> x \<and> b \<ge> y"
  by sorry

lemma solutions_linorder_strict:
  fixes a b x y :: nat
  assumes "solution (a, b)" "solution (x, y)"
  shows   "(a, b) = (x, y) \<or> a < x \<and> b < y \<or> a > x \<and> b > y"
  by sorry

lemma solutions_le_iff_pell_valuation_le:
  fixes a b x y :: nat
  assumes "solution (a, b)" "solution (x, y)"
  shows   "a \<le> x \<and> b \<le> y \<longleftrightarrow> pell_valuation (a, b) \<le> pell_valuation (x, y)"
  by sorry

lemma solutions_less_iff_pell_valuation_less:
  fixes a b x y :: nat
  assumes "solution (a, b)" "solution (x, y)"
  shows   "a < x \<and> b < y \<longleftrightarrow> pell_valuation (a, b) < pell_valuation (x, y)"
  by sorry


subsection \<open>The fundamental solution\<close>

text \<open>
  The \<^emph>\<open>fundamental solution\<close> is the non-trivial solution \<open>(x, y)\<close> with non-negative \<open>x\<close> and \<open>y\<close>
  for which the Pell valuation $x + y\sqrt{D}$ is minimal, or, equivalently, for which \<open>x\<close> and \<open>y\<close>
  are minimal.
\<close>
definition fund_sol :: "nat \<times> nat" where
  "fund_sol = (THE z::nat\<times>nat. is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution z)"

text \<open>
  The well-definedness of this follows from the injectivity of the Pell valuation and the fact
  that smaller Pell valuation of a solution is smaller than that of another iff the components
  are both smaller.
\<close>
theorem fund_sol_is_arg_min:
  "is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution fund_sol"
  by sorry

corollary
      fund_sol_is_nontriv_solution: "nontriv_solution fund_sol"
  and fund_sol_minimal:
        "nontriv_solution (a, b) \<Longrightarrow> pell_valuation fund_sol \<le> pell_valuation (int a, int b)"
  and fund_sol_minimal':
        "nontriv_solution (z :: nat \<times> nat) \<Longrightarrow> pell_valuation fund_sol \<le> pell_valuation z"
  by sorry

lemma fund_sol_minimal'':
  assumes "nontriv_solution z"
  shows   "fst fund_sol \<le> fst z" "snd fund_sol \<le> snd z"
  by sorry


subsection \<open>Group structure on solutions\<close>

text \<open>
  As was mentioned already, the Pell valuation function provides an injective map from
  solutions of Pell's equation into the ring $\mathbb{Z}[\sqrt{D}]$. We shall see now that
  the solutions are actually a subgroup of the multiplicative group of $\mathbb{Z}[\sqrt{D}]$ via
  the valuation function as a homomorphism:

    \<^item> The trivial solution \<open>(1, 0)\<close> has valuation \<open>1\<close>, which is the neutral element of
      $\mathbb{Z}[\sqrt{D}]^*$

    \<^item> Multiplication of two solutions $a + b \sqrt D$ and
      $x + y \sqrt D$ leads to $\bar x + \bar y\sqrt D$
      with $\bar x = xa + ybD$ and $\bar y = xb + ya$, which is again a solution.

    \<^item> The conjugate \<open>(x, -y)\<close> of a solution \<open>(x, y)\<close> is an inverse element to this
      multiplication operation, since $(x + y \sqrt D) (x - y \sqrt D) = 1$.
\<close>
definition pell_mul :: "('a :: comm_semiring_1 \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> ('a \<times> 'a)" where
  "pell_mul = (\<lambda>(a,b) (x,y). (x * a + y * b * of_nat D, x * b + y * a))"

definition pell_cnj :: "('a :: comm_ring_1 \<times> 'a) \<Rightarrow> 'a \<times> 'a" where
  "pell_cnj = (\<lambda>(a,b). (a, -b))"

lemma pell_cnj_snd_0 [simp]: "snd z = 0 \<Longrightarrow> pell_cnj z = z"
  by sorry

lemma pell_mul_commutes: "pell_mul z1 z2 = pell_mul z2 z1"
  by sorry

lemma pell_mul_assoc: "pell_mul z1 (pell_mul z2 z3) = pell_mul (pell_mul z1 z2) z3"
  by sorry

lemma pell_mul_trivial_left [simp]: "pell_mul (1, 0) z = z"
  by sorry

lemma pell_mul_trivial_right [simp]: "pell_mul z (1, 0) = z"
  by sorry

lemma pell_mul_trivial_left_nat [simp]: "pell_mul (Suc 0, 0) z = z"
  by sorry

lemma pell_mul_trivial_right_nat [simp]: "pell_mul z (Suc 0, 0) = z"
  by sorry

definition pell_power :: "('a :: comm_semiring_1 \<times> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a)" where
  "pell_power z n = ((\<lambda>z'. pell_mul z' z) ^^ n) (1, 0)"

lemma pell_power_0 [simp]: "pell_power z 0 = (1, 0)"
  by sorry

lemma pell_power_one [simp]: "pell_power (1, 0) n = (1, 0)"
  by sorry

lemma pell_power_one_right [simp]: "pell_power z 1 = z"
  by sorry

lemma pell_power_Suc: "pell_power z (Suc n) = pell_mul z (pell_power z n)"
  by sorry

lemma pell_power_add: "pell_power z (m + n) = pell_mul (pell_power z m) (pell_power z n)"
  by sorry

lemma pell_valuation_mult [simp]:
  "pell_valuation (pell_mul z1 z2) = pell_valuation z1 * pell_valuation z2"
  by sorry

lemma pell_valuation_mult_nat [simp]:
  "pell_valuation (case pell_mul z1 z2 of (a, b) \<Rightarrow> (int a, int b)) =
     pell_valuation z1 * pell_valuation z2"
  by sorry

lemma pell_valuation_trivial [simp]: "pell_valuation (1, 0) = 1"
  by sorry

lemma pell_valuation_trivial_nat [simp]: "pell_valuation (Suc 0, 0) = 1"
  by sorry

lemma pell_valuation_cnj: "pell_valuation (pell_cnj z) = fst z - snd z * sqrt D"
  by sorry

lemma pell_valuation_snd_0 [simp]: "pell_valuation (a, 0) = of_int a"
  by sorry

lemma pell_valuation_0_iff [simp]: "pell_valuation z = 0 \<longleftrightarrow> z = (0, 0)"
  by sorry

lemma pell_valuation_solution_pos_nat:
  fixes z :: "nat \<times> nat"
  assumes "solution z"
  shows   "pell_valuation z > 0"
  by sorry

lemma
  assumes "solution z"
  shows   pell_mul_cnj_right: "pell_mul z (pell_cnj z) = (1, 0)"
    and   pell_mul_cnj_left: "pell_mul (pell_cnj z) z = (1, 0)"
  by sorry

lemma pell_valuation_cnj_solution:
  fixes z :: "nat \<times> nat"
  assumes "solution z"
  shows   "pell_valuation (pell_cnj z) = 1 / pell_valuation z"
  by sorry

lemma pell_valuation_power [simp]: "pell_valuation (pell_power z n) = pell_valuation z ^ n"
  by sorry

lemma pell_valuation_power_nat [simp]:
  "pell_valuation (case pell_power z n of (a, b) \<Rightarrow> (int a, int b)) = pell_valuation z ^ n"
  by sorry

lemma pell_valuation_fund_sol_ge_2: "pell_valuation fund_sol \<ge> 2"
  by sorry


lemma solution_pell_mul [intro]:
  assumes "solution z1" "solution z2"
  shows   "solution (pell_mul z1 z2)"
  by sorry

lemma solution_pell_cnj [intro]:
  assumes "solution z"
  shows   "solution (pell_cnj z)"
  by sorry

lemma solution_pell_power [simp, intro]: "solution z \<Longrightarrow> solution (pell_power z n)"
  by sorry

lemma pell_mul_eq_trivial_nat_iff:
  "pell_mul z1 z2 = (Suc 0, 0) \<longleftrightarrow> z1 = (Suc 0, 0) \<and> z2 = (Suc 0, 0)"
  by sorry

lemma nontriv_solution_pell_nat_mul1:
  "solution (z1 :: nat \<times> nat) \<Longrightarrow> nontriv_solution z2 \<Longrightarrow> nontriv_solution (pell_mul z1 z2)"
  by sorry

lemma nontriv_solution_pell_nat_mul2:
  "nontriv_solution (z1 :: nat \<times> nat) \<Longrightarrow> solution z2 \<Longrightarrow> nontriv_solution (pell_mul z1 z2)"
  by sorry

lemma nontriv_solution_power_nat [intro]:
  assumes "nontriv_solution (z :: nat \<times> nat)" "n > 0"
  shows   "nontriv_solution (pell_power z n)"
  by sorry


subsection \<open>The different regions of the valuation function\<close>

text \<open>
  Next, we shall explore what happens to the valuation function for solutions \<open>(x, y)\<close> for
  different signs of \<open>x\<close> and \<open>y\<close>:

    \<^item> If \<open>x > 0\<close> and \<open>y > 0\<close>, we have  $x + y \sqrt D > 1$.

    \<^item> If \<open>x > 0\<close> and \<open>y < 0\<close>, we have $0 < x + y \sqrt D < 1$.

    \<^item> If \<open>x < 0\<close> and \<open>y > 0\<close>, we have $-1 < x + y \sqrt D < 0$.

    \<^item> If \<open>x < 0\<close> and \<open>y < 0\<close>, we have $x + y \sqrt D < -1$.

  In particular, this means that we can deduce the sign of \<open>x\<close> and \<open>y\<close> if we know in
  which of these four regions the valuation lies.
\<close>
lemma
  assumes "x > 0" "y > 0" "solution (x, y)"
  shows   pell_valuation_pos_pos: "pell_valuation (x, y) > 1"
    and   pell_valuation_pos_neg_aux: "pell_valuation (x, -y) \<in> {0<..<1}"
  by sorry

lemma pell_valuation_pos_neg:
  assumes "x > 0" "y < 0" "solution (x, y)"
  shows   "pell_valuation (x, y) \<in> {0<..<1}"
  by sorry

lemma pell_valuation_neg_neg:
  assumes "x < 0" "y < 0" "solution (x, y)"
  shows   "pell_valuation (x, y) < -1"
  by sorry

lemma pell_valuation_neg_pos:
  assumes "x < 0" "y > 0" "solution (x, y)"
  shows   "pell_valuation (x, y) \<in> {-1<..<0}"
  by sorry

lemma pell_valuation_solution_gt1D:
  assumes "solution z" "pell_valuation z > 1"
  shows   "fst z > 0 \<and> snd z > 0"
  by sorry


subsection \<open>Generating property of the fundamental solution\<close>

text \<open>
  We now show that the fundamental solution generates the set of the (non-negative) solutions
  in the sense that each solution is a power of the fundamental solution. Combined with the
  symmetry property that \<open>(x,y)\<close> is a solution iff \<open>(\<plusminus>x, \<plusminus>y)\<close> is a solution, this gives us
  a complete characterisation of all solutions of Pell's equation.
\<close>
definition nth_solution :: "nat \<Rightarrow> nat \<times> nat" where
  "nth_solution n = pell_power fund_sol n"

lemma pell_valuation_nth_solution [simp]:
  "pell_valuation (nth_solution n) = pell_valuation fund_sol ^ n"
  by sorry

theorem nth_solution_inj: "inj nth_solution"
  by sorry

theorem nth_solution_sound [intro]: "solution (nth_solution n)"
  by sorry

theorem nth_solution_sound' [intro]: "n > 0 \<Longrightarrow> nontriv_solution (nth_solution n)"
  by sorry

theorem nth_solution_complete:
  fixes z :: "nat \<times> nat"
  assumes "solution z"
  shows   "z \<in> range nth_solution"
  by sorry

corollary solution_iff_nth_solution:
  fixes z :: "nat \<times> nat"
  shows "solution z \<longleftrightarrow> z \<in> range nth_solution"
  by sorry

corollary solution_iff_nth_solution':
  fixes z :: "int \<times> int"
  shows "solution (a, b) \<longleftrightarrow> (nat \<bar>a\<bar>, nat \<bar>b\<bar>) \<in> range nth_solution"
  by sorry

corollary infinite_solutions: "infinite {z :: nat \<times> nat. solution z}"
  by sorry

corollary infinite_solutions': "infinite {z :: int \<times> int. solution z}"
  by sorry


lemma strict_mono_pell_valuation_nth_solution: "strict_mono (pell_valuation \<circ> nth_solution)"
  by sorry

lemma strict_mono_nth_solution:
  "strict_mono (fst \<circ> nth_solution)" "strict_mono (snd \<circ> nth_solution)"
  by sorry

end


subsection \<open>The case of an ``almost square'' parameter\<close>

text \<open>
  If \<open>D\<close> is equal to \<open>a\<^sup>2 - 1\<close> for some \<open>a > 1\<close>, we have a particularly simple case
  where the fundamental solution is simply \<open>(1, a)\<close>.
\<close>

context
  fixes a :: nat
  assumes a: "a > 1"
begin

lemma pell_square_minus1: "pell (a\<^sup>2 - Suc 0)"
  by sorry

interpretation pell "a\<^sup>2 - Suc 0"
  by (rule pell_square_minus1)

lemma fund_sol_square_minus1: "fund_sol = (a, 1)"
  by sorry

end


subsection \<open>Alternative presentation of the main results\<close>

theorem pell_solutions:
 fixes D :: nat
 assumes "\<nexists>k. D = k\<^sup>2"
 obtains x\<^sub>0 y\<^sub>0 :: nat
 where   "\<forall>(x::int) (y::int).
            x\<^sup>2 - D * y\<^sup>2 = 1 \<longleftrightarrow>
            (\<exists>n::nat. nat \<bar>x\<bar> + sqrt D * nat \<bar>y\<bar> = (x\<^sub>0 + sqrt D * y\<^sub>0) ^ n)"
  by sorry

corollary pell_solutions_infinite:
 fixes D :: nat
 assumes "\<nexists>k. D = k\<^sup>2"
 shows   "infinite {(x :: int, y :: int). x\<^sup>2 - D * y\<^sup>2 = 1}"
  by sorry

end