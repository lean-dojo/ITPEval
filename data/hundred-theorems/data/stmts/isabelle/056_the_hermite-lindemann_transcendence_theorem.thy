(*
  File:     Hermite_Lindemann.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>The Hermite--Lindemann--Weierstra\ss Transcendence Theorem\<close>
theory Hermite_Lindemann
imports 
  Pi_Transcendental.Pi_Transcendental
  Algebraic_Numbers.Algebraic_Numbers
  Algebraic_Integer_Divisibility
  More_Min_Int_Poly
  Complex_Lexorder
  More_Polynomial_HLW
  More_Multivariate_Polynomial_HLW
  More_Algebraic_Numbers_HLW
  Misc_HLW
begin

hide_const (open) Henstock_Kurzweil_Integration.content  Module.smult


text \<open>
  The Hermite--Lindemann--Weierstra\ss theorem answers questions about the transcendence of
  the exponential function and other related complex functions. It proves that a large number of
  combinations of exponentials is always transcendental.

  A first (much weaker) version of the theorem was proven by Hermite. Lindemann and Weierstra\ss then
  successively generalised it shortly afterwards, and finally Baker gave another, arguably more
  elegant formulation (which is the one that we will prove, and then derive the traditional version
  from it).

  To honour the contributions of all three of these 19th-century mathematicians, I refer to the
  theorem as the Hermite--Lindemann--Weierstra\ss theorem, even though in other literature it is
  often called Hermite--Lindemann or Lindemann--Weierstra\ss. To keep things short, the Isabelle
  name of the theorem, however, will omit Weierstra\ss's name.
\<close>

subsection \<open>Main proof\<close>

text \<open>
  Following Baker, We first prove the following special form of the theorem:
  Let $m > 0$ and $q_1, \ldots, q_m \in\mathbb{Z}[X]$ be irreducible, non-constant,
  and pairwise coprime polynomials. Let $\beta_1, \ldots, \beta_m$ be non-zero integers. Then
  \[\sum_{i=1}^m \beta_i \sum_{q_i(\alpha) = 0} e^\alpha \neq 0\]

  The difference to the final theorem is that

    \<^enum> The coefficients $\beta_i$ are non-zero integers (as opposed to arbitrary algebraic numbers)

    \<^enum> The exponents $\alpha_i$ occur in full sets of conjugates, and each set has the same
      coefficient.

  In a similar fashion to the proofs of the transcendence of \<open>e\<close> and \<open>\<pi>\<close>, we define some number
  $J$ depending on the $\alpha_i$ and $\beta_i$ and an arbitrary sufficiently large prime \<open>p\<close>. We
  then show that, on one hand, $J$ is an integer multiple of $(p-1)!$, but on the other hand it
  is bounded from above by a term of the form $C_1 \cdot C_2^p$. This is then clearly a
  contradiction if \<open>p\<close> is chosen large enough.
\<close>

lemma Hermite_Lindemann_aux1:
  fixes P :: "int poly set" and \<beta> :: "int poly \<Rightarrow> int"
  assumes "finite P" and "P \<noteq> {}"
  assumes distinct: "pairwise Rings.coprime P"
  assumes irred: "\<And>p. p \<in> P \<Longrightarrow> irreducible p"
  assumes nonconstant: "\<And>p. p \<in> P \<Longrightarrow> Polynomial.degree p > 0"
  assumes \<beta>_nz: "\<And>p. p \<in> P \<Longrightarrow> \<beta> p \<noteq> 0"
  defines "Roots \<equiv> (\<lambda>p. {\<alpha>::complex. poly (of_int_poly p) \<alpha> = 0})"
  shows   "(\<Sum>p\<in>P. of_int (\<beta> p) * (\<Sum>\<alpha>\<in>Roots p. exp \<alpha>)) \<noteq> 0"
  by sorry


subsection \<open>Removing the restriction of full sets of conjugates\<close>

text \<open>
  We will now remove the restriction that the $\alpha_i$ must occur in full sets of conjugates
  by multiplying the equality with all permutations of roots.
\<close>
lemma Hermite_Lindemann_aux2:
  fixes X :: "complex set" and \<beta> :: "complex \<Rightarrow> int"
  assumes "finite X"
  assumes nz:   "\<And>x. x \<in> X \<Longrightarrow> \<beta> x \<noteq> 0"
  assumes alg:  "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes sum0: "(\<Sum>x\<in>X. of_int (\<beta> x) * exp x) = 0"
  shows   "X = {}"
  by sorry


subsection \<open>Removing the restriction to integer coefficients\<close>

text \<open>
  Next, we weaken the restriction that the $\beta_i$ must be integers to the restriction
  that they must be rationals. This is done simply by multiplying with the least common multiple
  of the demoninators.
\<close>
lemma Hermite_Lindemann_aux3:
  fixes X :: "complex set" and \<beta> :: "complex \<Rightarrow> rat"
  assumes "finite X"
  assumes nz:   "\<And>x. x \<in> X \<Longrightarrow> \<beta> x \<noteq> 0"
  assumes alg:  "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes sum0: "(\<Sum>x\<in>X. of_rat (\<beta> x) * exp x) = 0"
  shows   "X = {}"
  by sorry

text \<open>
  Next, we weaken the restriction that the $\beta_i$ must be rational to them being algebraic.
  Similarly to before, this is done by multiplying over all possible permutations of the $\beta_i$
  (in some sense) to introduce more symmetry, from which it then follows by the fundamental theorem
  of symmetric polynomials that the resulting coefficients are rational.
\<close>
lemma Hermite_Lindemann_aux4:
  fixes \<beta> :: "complex \<Rightarrow> complex"
  assumes [intro]: "finite X"
  assumes alg1: "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes alg2: "\<And>x. x \<in> X \<Longrightarrow> algebraic (\<beta> x)"
  assumes nz:   "\<And>x. x \<in> X \<Longrightarrow> \<beta> x \<noteq> 0"
  assumes sum0: "(\<Sum>x\<in>X. \<beta> x * exp x) = 0"
  shows   "X = {}"
  by sorry


subsection \<open>The final theorem\<close>

text \<open>
  We now additionally allow some of the $\beta_i$ to be zero:
\<close>
lemma Hermite_Lindemann':
  fixes \<beta> :: "complex \<Rightarrow> complex"
  assumes "finite X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> algebraic x"
  assumes "\<And>x. x \<in> X \<Longrightarrow> algebraic (\<beta> x)"
  assumes "(\<Sum>x\<in>X. \<beta> x * exp x) = 0"
  shows   "\<forall>x\<in>X. \<beta> x = 0"
  by sorry

text \<open>
  Lastly, we switch to indexed summation in order to obtain a version of the theorem that
  is somewhat nicer to use:
\<close>
theorem Hermite_Lindemann:
  fixes \<alpha> \<beta> :: "'a \<Rightarrow> complex"
  assumes "finite I"
  assumes "\<And>x. x \<in> I \<Longrightarrow> algebraic (\<alpha> x)"
  assumes "\<And>x. x \<in> I \<Longrightarrow> algebraic (\<beta> x)"
  assumes "inj_on \<alpha> I"
  assumes "(\<Sum>x\<in>I. \<beta> x * exp (\<alpha> x)) = 0"
  shows   "\<forall>x\<in>I. \<beta> x = 0"
  by sorry

text \<open>
  The following version using lists instead of sequences is even more convenient to use
  in practice:
\<close>
corollary Hermite_Lindemann_list:
  fixes xs :: "(complex \<times> complex) list"
  assumes alg:      "\<forall>(x,y)\<in>set xs. algebraic x \<and> algebraic y"
  assumes distinct: "distinct (map snd xs)"
  assumes sum0:     "(\<Sum>(c,\<alpha>)\<leftarrow>xs. c * exp \<alpha>) = 0"
  shows   "\<forall>c\<in>(fst ` set xs). c = 0"
  by sorry


subsection \<open>The traditional formulation of the theorem\<close>

text \<open>
  What we proved above was actually Baker's reformulation of the theorem. Thus, we now also derive
  the original one, which uses linear independence and algebraic independence.

  It states that if $\alpha_1, \ldots, \alpha_n$ are algebraic numbers that are linearly
  independent over \<open>\<int>\<close>, then $e^{\alpha_1}, \ldots, e^{\alpha_n}$ are algebraically independent
  over \<open>\<rat>\<close>.
\<close>

text \<open>
  Linear independence over the integers is just independence of a set of complex numbers when
  viewing the complex numbers as a \<open>\<int>\<close>-module.
\<close>
definition linearly_independent_over_int :: "'a :: field_char_0 set \<Rightarrow> bool" where
  "linearly_independent_over_int = module.independent (\<lambda>r x. of_int r * x)"

text \<open>
  Algebraic independence over the rationals means that the given set \<open>X\<close> of numbers fulfils
  no non-trivial polynomial equation with rational coefficients, i.e. there is no non-zero
  multivariate polynomial with rational coefficients that, when inserting the numbers from \<open>X\<close>,
  becomes zero.

  Note that we could easily replace `rational coefficients' with `algebraic coefficients' here
  and the proof would still go through without any modifications.
\<close>
definition algebraically_independent_over_rat :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: field_char_0) \<Rightarrow> bool" where
  "algebraically_independent_over_rat n a \<longleftrightarrow>
     (\<forall>p. vars p \<subseteq> {..<n} \<and> (\<forall>m. coeff p m \<in> \<rat>) \<and> insertion a p = 0 \<longrightarrow> p = 0)"

corollary Hermite_Lindemann_original:
  fixes n :: nat and \<alpha> :: "nat \<Rightarrow> complex"
  assumes "inj_on \<alpha> {..<n}"
  assumes "\<And>i. i < n \<Longrightarrow> algebraic (\<alpha> i)"
  assumes "linearly_independent_over_int (\<alpha> ` {..<n})"
  shows   "algebraically_independent_over_rat n (\<lambda>i. exp (\<alpha> i))"
  by sorry


subsection \<open>Simple corollaries\<close>

text \<open>
  Now, we derive all the usual obvious corollaries of the theorem in the obvious way.

  First, the exponential of a non-zero algebraic number is transcendental.
\<close>
corollary algebraic_exp_complex_iff:
  assumes "algebraic x"
  shows   "algebraic (exp x :: complex) \<longleftrightarrow> x = 0"
  by sorry

text \<open>
  More generally, any sum of exponentials with algebraic coefficients and exponents is
  transcendental if the exponents are all distinct and non-zero and at least one coefficient
  is non-zero.
\<close>
corollary sum_of_exp_transcendentalI:
  fixes xs :: "(complex \<times> complex) list"
  assumes "\<forall>(x,y)\<in>set xs. algebraic x \<and> algebraic y \<and> y \<noteq> 0"
  assumes "\<exists>x\<in>fst`set xs. x \<noteq> 0"
  assumes distinct: "distinct (map snd xs)"
  shows   "\<not>algebraic (\<Sum>(c,\<alpha>)\<leftarrow>xs. c * exp \<alpha>)"
  by sorry

text \<open>
  Any complex logarithm of an algebraic number other than 1 is transcendental
  (no matter which branch cut).
\<close>
corollary transcendental_complex_logarithm:
  assumes "algebraic x" "exp y = (x :: complex)" "x \<noteq> 1"
  shows   "\<not>algebraic y"
  by sorry

text \<open>
  In particular, this holds for the standard branch of the logarithm.
\<close>
corollary transcendental_Ln:
  assumes "algebraic x" "x \<noteq> 0" "x \<noteq> 1"
  shows   "\<not>algebraic (Ln x)"
  by sorry

text \<open>
  The transcendence of \<open>e\<close> and \<open>\<pi>\<close>, which I have already formalised directly in other AFP
  entries, now follows as a simple corollary.
\<close>
corollary exp_1_complex_transcendental: "\<not>algebraic (exp 1 :: complex)"
  by sorry

corollary pi_transcendental: "\<not>algebraic pi"
  by sorry


subsection \<open>Transcendence of the trigonometric and hyperbolic functions\<close>

text \<open>
  In a similar fashion, we can also prove the transcendence of all the trigonometric and
  hyperbolic functions such as $\sin$, $\tan$, $\sinh$, $\arcsin$, etc.
\<close>

lemma transcendental_sinh:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (sinh z :: complex)"
  by sorry

lemma transcendental_cosh:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (cosh z :: complex)"
  by sorry

lemma transcendental_sin:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (sin z :: complex)"
  by sorry

lemma transcendental_cos:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (cos z :: complex)"
  by sorry

(* TODO: Move? *)
lemma tan_square_neq_neg1: "tan (z :: complex) ^ 2 \<noteq> -1"
  by sorry

lemma transcendental_tan:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (tan z :: complex)"
  by sorry

lemma transcendental_cot:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (cot z :: complex)"
  by sorry

lemma transcendental_tanh:
  assumes "algebraic z" "z \<noteq> 0" "cosh z \<noteq> 0"
  shows   "\<not>algebraic (tanh z :: complex)"
  by sorry

lemma transcendental_Arcsin:
  assumes "algebraic z" "z \<noteq> 0"
  shows   "\<not>algebraic (Arcsin z)"
  by sorry

lemma transcendental_Arccos:
  assumes "algebraic z" "z \<noteq> 1"
  shows   "\<not>algebraic (Arccos z)"
  by sorry

lemma transcendental_Arctan:
  assumes "algebraic z" "z \<notin> {0, \<i>, -\<i>}"
  shows   "\<not>algebraic (Arctan z)"
  by sorry

end
