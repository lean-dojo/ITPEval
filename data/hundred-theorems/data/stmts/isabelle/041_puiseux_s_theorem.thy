(*
  File:    Formal_Puiseux_Series.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Formal Puiseux Series\<close>
theory Formal_Puiseux_Series
  imports FPS_Hensel
begin

subsection \<open>Auxiliary facts and definitions\<close>

lemma div_dvd_self:
  fixes a b :: "'a :: {semidom_divide}"
  shows "b dvd a \<Longrightarrow> a div b dvd a"
  by sorry

lemma quotient_of_int [simp]: "quotient_of (of_int n) = (n, 1)"
  by sorry

lemma of_int_div_of_int_in_Ints_iff:
  "(of_int n / of_int m :: 'a :: field_char_0) \<in> \<int> \<longleftrightarrow> m = 0 \<or> m dvd n"
  by sorry

lemma rat_eq_quotientD:
  assumes "r = rat_of_int a / rat_of_int b" "b \<noteq> 0"
  shows   "fst (quotient_of r) dvd a" "snd (quotient_of r) dvd b"
  by sorry

lemma quotient_of_denom_add_dvd:
  "snd (quotient_of (x + y)) dvd snd (quotient_of x) * snd (quotient_of y)"
  by sorry

lemma quotient_of_denom_diff_dvd:
  "snd (quotient_of (x - y)) dvd snd (quotient_of x) * snd (quotient_of y)"
  by sorry


definition supp :: "('a \<Rightarrow> ('b :: zero)) \<Rightarrow> 'a set" where
  "supp f = f -` (-{0})"

lemma supp_0 [simp]: "supp (\<lambda>_. 0) = {}"
  and supp_const: "supp (\<lambda>_. c) = (if c = 0 then {} else UNIV)"
  and supp_singleton [simp]: "c \<noteq> 0 \<Longrightarrow> supp (\<lambda>x. if x = d then c else 0) = {d}"
  by sorry

lemma supp_uminus [simp]: "supp (\<lambda>x. -f x :: 'a :: group_add) = supp f"
  by sorry


subsection \<open>Definition\<close>

text \<open>
  Similarly to formal power series $R[[X]]$ and formal Laurent series $R((X))$, we define the ring
  of formal Puiseux series $R\{\{X\}\}$ as functions from the rationals into a ring such that

    \<^enum> the support is bounded from below, and 

    \<^enum> the denominators of the numbers in the support have a common multiple other than 0

  One can also think of a formal Puiseux series in the paramter $X$ as a formal Laurent series
  in the parameter $X^{1/d}$ for some positive integer $d$. This is often written in the
  following suggestive notation:
  \[ R\{\{X\}\} = \bigcup_{d\geq 1} R((X^{1/d})) \]

  Many operations will be defined in terms of this correspondence between Puiseux and Laurent
  series, and many of the simple properties proven that way.
\<close>

definition is_fpxs :: "(rat \<Rightarrow> 'a :: zero) \<Rightarrow> bool" where
  "is_fpxs f \<longleftrightarrow> bdd_below (supp f) \<and> (LCM r\<in>supp f. snd (quotient_of r)) \<noteq> 0"

typedef (overloaded) 'a fpxs = "{f::rat \<Rightarrow> 'a :: zero. is_fpxs f}"
  morphisms fpxs_nth Abs_fpxs
  by (rule exI[of _ "\<lambda>_. 0"]) (auto simp: is_fpxs_def supp_def)

setup_lifting type_definition_fpxs

lemma fpxs_ext: "(\<And>r. fpxs_nth f r = fpxs_nth g r) \<Longrightarrow> f = g"
  by sorry

lemma fpxs_eq_iff: "f = g \<longleftrightarrow> (\<forall>r. fpxs_nth f r = fpxs_nth g r)"
  by sorry

lift_definition fpxs_supp :: "'a :: zero fpxs \<Rightarrow> rat set" is supp .

lemma fpxs_supp_altdef: "fpxs_supp f = {x. fpxs_nth f x \<noteq> 0}"
  by sorry


text \<open>
  The following gives us the ``root order'' of \<open>f\<close>i, i.e. the smallest positive integer \<open>d\<close>
  such that \<open>f\<close> is in $R((X^{1/p}))$.
\<close>
lift_definition fpxs_root_order :: "'a :: zero fpxs \<Rightarrow> nat" is
  "\<lambda>f. nat (LCM r\<in>supp f. snd (quotient_of r))" .

lemma fpxs_root_order_pos [simp]: "fpxs_root_order f > 0"
  by sorry

lemma fpxs_root_order_nonzero [simp]: "fpxs_root_order f \<noteq> 0"
  by sorry


text \<open>
  Let \<open>d\<close> denote the root order of a Puiseux series \<open>f\<close>, i.e. the smallest number \<open>d\<close> such that
  all monomials with non-zero coefficients can be written in the form $X^{n/d}$ for some \<open>n\<close>.
  Then \<open>f\<close> can be written as a Laurent series in \<open>X^{1/d}\<close>. The following operation gives us
  this Laurent series.
\<close>
lift_definition fls_of_fpxs :: "'a :: zero fpxs \<Rightarrow> 'a fls" is
  "\<lambda>f n. f (of_int n / of_int (LCM r\<in>supp f. snd (quotient_of r)))"
proof -
  fix f :: "rat \<Rightarrow> 'a"
  assume f: "is_fpxs f"
  hence "bdd_below (supp f)"
    by (auto simp: is_fpxs_def)
  then obtain r0 where "\<forall>x\<in>supp f. r0 \<le> x"
    by (auto simp: bdd_below_def)
  hence r0: "f x = 0" if "x < r0" for x
    using that by (auto simp: supp_def vimage_def)
  define d :: int where "d = (LCM r\<in>supp f. snd (quotient_of r))"
  have "d \<ge> 0" by (simp add: d_def)
  moreover have "d \<noteq> 0"
    using f by (auto simp: d_def is_fpxs_def)
  ultimately have "d > 0" by linarith

  have *: "f (of_int n / of_int d) = 0" if "n < \<lfloor>r0 * of_int d\<rfloor>" for n
  proof -
    have "rat_of_int n < r0 * rat_of_int d"
      using that by linarith
    thus ?thesis
      using \<open>d > 0\<close> by (intro r0) (auto simp: field_simps)
  qed
  have "eventually (\<lambda>n. n > -\<lfloor>r0 * of_int d\<rfloor>) at_top"
    by (rule eventually_gt_at_top)
  hence "eventually (\<lambda>n. f (of_int (-n) / of_int d) = 0) at_top"
    by (eventually_elim) (rule *, auto)
  hence "eventually (\<lambda>n. f (of_int (-int n) / of_int d) = 0) at_top"
    by (rule eventually_compose_filterlim) (rule filterlim_int_sequentially)
  thus "eventually (\<lambda>n. f (of_int (-int n) / of_int d) = 0) cofinite"
    by (simp add: cofinite_eq_sequentially)
qed

lemma fls_nth_of_fpxs:
  "fls_nth (fls_of_fpxs f) n = fpxs_nth f (of_int n / of_nat (fpxs_root_order f))"
  by sorry


subsection \<open>Basic algebraic typeclass instances\<close>

instantiation fpxs :: (zero) zero
begin

lift_definition zero_fpxs :: "'a fpxs" is "\<lambda>r::rat. 0 :: 'a"
  by (auto simp: is_fpxs_def supp_def)

instance ..

end

instantiation fpxs :: ("{one, zero}") one
begin

lift_definition one_fpxs :: "'a fpxs" is "\<lambda>r::rat. if r = 0 then 1 else 0 :: 'a"
  by (cases "(1 :: 'a) = 0") (auto simp: is_fpxs_def cong: if_cong)

instance ..

end

lemma fls_of_fpxs_0 [simp]: "fls_of_fpxs 0 = 0"
  by sorry

lemma fpxs_nth_0 [simp]: "fpxs_nth 0 r = 0"
  by sorry

lemma fpxs_nth_1: "fpxs_nth 1 r = (if r = 0 then 1 else 0)"
  by sorry

lemma fpxs_nth_1': "fpxs_nth 1 0 = 1" "r \<noteq> 0 \<Longrightarrow> fpxs_nth 1 r = 0"
  by sorry

instantiation fpxs :: (monoid_add) monoid_add
begin

lift_definition plus_fpxs :: "'a fpxs \<Rightarrow> 'a fpxs \<Rightarrow> 'a fpxs" is
  "\<lambda>f g x. f x + g x"
proof -
  fix f g :: "rat \<Rightarrow> 'a"
  assume fg: "is_fpxs f" "is_fpxs g"
  show "is_fpxs (\<lambda>x. f x + g x)"
    unfolding is_fpxs_def
  proof
    have supp: "supp (\<lambda>x. f x + g x) \<subseteq> supp f \<union> supp g"
      by (auto simp: supp_def)
    show "bdd_below (supp (\<lambda>x. f x + g x))"
      by (rule bdd_below_mono[OF _ supp]) (use fg in \<open>auto simp: is_fpxs_def\<close>)
    have "(LCM r\<in>supp (\<lambda>x. f x + g x). snd (quotient_of r)) dvd
            (LCM r\<in>supp f \<union> supp g. snd (quotient_of r))"
      by (intro Lcm_subset image_mono supp)
    also have "\<dots> = lcm (LCM r\<in>supp f. snd (quotient_of r)) (LCM r\<in>supp g. snd (quotient_of r))"
      unfolding image_Un Lcm_Un ..
    finally have "(LCM r\<in>supp (\<lambda>x. f x + g x). snd (quotient_of r)) dvd
                    lcm (LCM r\<in>supp f. snd (quotient_of r)) (LCM r\<in>supp g. snd (quotient_of r))" .
    moreover have "lcm (LCM r\<in>supp f. snd (quotient_of r)) (LCM r\<in>supp g. snd (quotient_of r)) \<noteq> 0"
      using fg by (auto simp: is_fpxs_def)
    ultimately show "(LCM r\<in>supp (\<lambda>x. f x + g x). snd (quotient_of r)) \<noteq> 0"
      by auto
  qed
qed

instance 
  by standard (transfer; simp add: algebra_simps fun_eq_iff)+

end

instance fpxs :: (comm_monoid_add) comm_monoid_add
proof
  fix f g :: "'a fpxs"
  show "f + g = g + f"
    by transfer (auto simp: add_ac)
qed simp_all

lemma fpxs_nth_add [simp]: "fpxs_nth (f + g) r = fpxs_nth f r + fpxs_nth g r"
  by sorry

lift_definition fpxs_of_fls :: "'a :: zero fls \<Rightarrow> 'a fpxs" is
  "\<lambda>f r. if r \<in> \<int> then f \<lfloor>r\<rfloor> else 0"
proof -
  fix f :: "int \<Rightarrow> 'a"
  assume "eventually (\<lambda>n. f (-int n) = 0) cofinite"
  hence "eventually (\<lambda>n. f (-int n) = 0) at_top"
    by (simp add: cofinite_eq_sequentially)
  then obtain N where N: "f (-int n) = 0" if "n \<ge> N" for n
    by (auto simp: eventually_at_top_linorder)
  
  show "is_fpxs (\<lambda>r. if r \<in> \<int> then f \<lfloor>r\<rfloor> else 0)"
    unfolding is_fpxs_def
  proof
    have "bdd_below {-(of_nat N::rat)..}"
      by simp
    moreover have "supp (\<lambda>r::rat. if r \<in> \<int> then f \<lfloor>r\<rfloor> else 0) \<subseteq> {-of_nat N..}"
    proof
      fix r :: rat assume "r \<in> supp (\<lambda>r. if r \<in> \<int> then f \<lfloor>r\<rfloor> else 0)"
      then obtain m where [simp]: "r = of_int m" "f m \<noteq> 0"
        by (auto simp: supp_def elim!: Ints_cases split: if_splits)
      have "m \<ge> -int N"
        using N[of "nat (-m)"] by (cases "m \<ge> 0"; cases "-int N \<le> m") (auto simp: le_nat_iff)
      thus "r \<in> {-of_nat N..}" by simp
    qed
    ultimately show "bdd_below (supp (\<lambda>r::rat. if r \<in> \<int> then f \<lfloor>r\<rfloor> else 0))"
      by (rule bdd_below_mono)
  next
    have "(LCM r\<in>supp (\<lambda>r. if r \<in> \<int> then f \<lfloor>r\<rfloor> else 0). snd (quotient_of r)) dvd 1"
      by (intro Lcm_least) (auto simp: supp_def elim!: Ints_cases split: if_splits)
    thus "(LCM r\<in>supp (\<lambda>r. if r \<in> \<int> then f \<lfloor>r\<rfloor> else 0). snd (quotient_of r)) \<noteq> 0"
      by (intro notI) simp
  qed
qed

instantiation fpxs :: (group_add) group_add
begin

lift_definition uminus_fpxs :: "'a fpxs \<Rightarrow> 'a fpxs" is "\<lambda>f x. -f x"
  by (auto simp: is_fpxs_def)

definition minus_fpxs :: "'a fpxs \<Rightarrow> 'a fpxs \<Rightarrow> 'a fpxs" where
  "minus_fpxs f g = f + (-g)"

instance proof
  fix f :: "'a fpxs"
  show "-f + f = 0"
    by transfer auto
qed (auto simp: minus_fpxs_def)

end

lemma fpxs_nth_uminus [simp]: "fpxs_nth (-f) r = -fpxs_nth f r"
  by sorry

lemma fpxs_nth_minus [simp]: "fpxs_nth (f - g) r = fpxs_nth f r - fpxs_nth g r"
  by sorry

lemma fpxs_of_fls_eq_iff [simp]: "fpxs_of_fls f = fpxs_of_fls g \<longleftrightarrow> f = g"
  by sorry

lemma fpxs_of_fls_0 [simp]: "fpxs_of_fls 0 = 0"
  by sorry

lemma fpxs_of_fls_1 [simp]: "fpxs_of_fls 1 = 1"
  by sorry

lemma fpxs_of_fls_add [simp]: "fpxs_of_fls (f + g) = fpxs_of_fls f + fpxs_of_fls g"
  by sorry

lemma fps_to_fls_sum [simp]: "fps_to_fls (sum f A) = (\<Sum>x\<in>A. fps_to_fls (f x))"
  by sorry

lemma fpxs_of_fls_sum [simp]: "fpxs_of_fls (sum f A) = (\<Sum>x\<in>A. fpxs_of_fls (f x))"
  by sorry

lemma fpxs_nth_of_fls:
  "fpxs_nth (fpxs_of_fls f) r = (if r \<in> \<int> then fls_nth f \<lfloor>r\<rfloor> else 0)"
  by sorry

lemma fpxs_of_fls_eq_0_iff [simp]: "fpxs_of_fls f = 0 \<longleftrightarrow> f = 0"
  by sorry

lemma fpxs_of_fls_eq_1_iff [simp]: "fpxs_of_fls f = 1 \<longleftrightarrow> f = 1"
  by sorry

lemma fpxs_root_order_of_fls [simp]: "fpxs_root_order (fpxs_of_fls f) = 1"
  by sorry



subsection \<open>The substitution $X \mapsto X^r$\<close>

text \<open>
  This operation turns a formal Puiseux series $f(X)$ into $f(X^r)$, where
  $r$ can be any positive rational number:
\<close>
lift_definition fpxs_compose_power :: "'a :: zero fpxs \<Rightarrow> rat \<Rightarrow> 'a fpxs" is
  "\<lambda>f r x. if r > 0 then f (x / r) else 0"
proof -
  fix f :: "rat \<Rightarrow> 'a" and r :: rat
  assume f: "is_fpxs f"
  have "is_fpxs (\<lambda>x. f (x / r))" if "r > 0"
    unfolding is_fpxs_def
  proof
    define r' where "r' = inverse r"
    have "r' > 0"
      using \<open>r > 0\<close> by (auto simp: r'_def)
    have "(\<lambda>x. x / r') ` supp f = supp (\<lambda>x. f (x * r'))"
      using \<open>r' > 0\<close> by (auto simp: supp_def image_iff vimage_def field_simps)
    hence eq: "(\<lambda>x. x * r) ` supp f = supp (\<lambda>x. f (x / r))"
      using \<open>r > 0\<close> by (simp add: r'_def field_simps)

    from f have "bdd_below (supp f)"
      by (auto simp: is_fpxs_def)
    hence "bdd_below ((\<lambda>x. x * r) ` supp f)"
      using \<open>r > 0\<close> by (intro bdd_below_image_mono) (auto simp: mono_def divide_right_mono)
    also note eq
    finally show "bdd_below (supp (\<lambda>x. f (x / r)))" .

    define a b where "a = fst (quotient_of r)" and "b = snd (quotient_of r)"
    have "b > 0" by (simp add: b_def quotient_of_denom_pos')
    have [simp]: "quotient_of r = (a, b)"
      by (simp add: a_def b_def)
    have "r = of_int a / of_int b"
      by (simp add: quotient_of_div)
    with \<open>r > 0\<close> and \<open>b > 0\<close> have \<open>a > 0\<close>
      by (simp add: field_simps)

    have "(LCM r\<in>supp (\<lambda>x. f (x / r)). snd (quotient_of r)) =
            (LCM x\<in>supp f. snd (quotient_of (x * r)))"
      by (simp add: eq [symmetric] image_image)
    also have "\<dots> dvd (LCM x\<in>supp f. snd (quotient_of x) * b)"
      using \<open>a > 0\<close> \<open>b > 0\<close>
      by (intro Lcm_mono)
         (simp add: rat_times_code case_prod_unfold Let_def Rat.normalize_def
                    quotient_of_denom_pos' div_dvd_self)
    also have "\<dots> dvd normalize (b * (LCM x\<in>supp f. snd (quotient_of x)))"
    proof (cases "supp f = {}")
      case False
      thus ?thesis using Lcm_mult[of "(\<lambda>x. snd (quotient_of x)) ` supp f" b]
        by (simp add: mult_ac image_image)
    qed auto
    hence "(LCM x\<in>supp f. snd (quotient_of x) * b) dvd
             b * (LCM x\<in>supp f. snd (quotient_of x))" by simp
    finally show "(LCM r\<in>supp (\<lambda>x. f (x / r)). snd (quotient_of r)) \<noteq> 0"
      using \<open>b > 0\<close> f by (auto simp: is_fpxs_def)
  qed
  thus "is_fpxs (\<lambda>x. if r > 0 then f (x / r) else 0)"
    by (cases "r > 0") (auto simp: is_fpxs_def supp_def)
qed

lemma fpxs_as_fls:
  "fpxs_compose_power (fpxs_of_fls (fls_of_fpxs f)) (1 / of_nat (fpxs_root_order f)) = f"
  by sorry

lemma fpxs_compose_power_0 [simp]: "fpxs_compose_power 0 r = 0"
  by sorry

lemma fpxs_compose_power_1 [simp]: "r > 0 \<Longrightarrow> fpxs_compose_power 1 r = 1"
  by sorry

lemma fls_of_fpxs_eq_0_iff [simp]: "fls_of_fpxs x = 0 \<longleftrightarrow> x = 0"
  by sorry

lemma fpxs_of_fls_compose_power [simp]:
  "fpxs_of_fls (fls_compose_power f d) = fpxs_compose_power (fpxs_of_fls f) (of_nat d)"
  by sorry

lemma fpxs_compose_power_add [simp]:
  "fpxs_compose_power (f + g) r = fpxs_compose_power f r + fpxs_compose_power g r"
  by sorry

lemma fpxs_compose_power_distrib:
  "r1 > 0 \<or> r2 > 0 \<Longrightarrow> 
     fpxs_compose_power (fpxs_compose_power f r1) r2 = fpxs_compose_power f (r1 * r2)"
  by sorry

lemma fpxs_compose_power_divide_right:
  "r1 > 0 \<Longrightarrow> r2 > 0 \<Longrightarrow> 
     fpxs_compose_power f (r1 / r2) = fpxs_compose_power (fpxs_compose_power f r1) (inverse r2)"
  by sorry

lemma fpxs_compose_power_1_right [simp]: "fpxs_compose_power f 1 = f"
  by sorry

lemma fpxs_compose_power_eq_iff [simp]:
  assumes "r > 0"
  shows   "fpxs_compose_power f r = fpxs_compose_power g r \<longleftrightarrow> f = g"
  by sorry

lemma fpxs_compose_power_eq_1_iff [simp]:
  assumes "l > 0"
  shows   "fpxs_compose_power p l = 1 \<longleftrightarrow> p = 1"
  by sorry

lemma fpxs_compose_power_eq_0_iff [simp]:
  assumes "r > 0"
  shows   "fpxs_compose_power f r = 0 \<longleftrightarrow> f = 0"
  by sorry

lemma fls_of_fpxs_of_fls [simp]: "fls_of_fpxs (fpxs_of_fls f) = f"
  by sorry

lemma fpxs_as_fls':
  assumes "fpxs_root_order f dvd d" "d > 0"
  obtains f' where "f = fpxs_compose_power (fpxs_of_fls f') (1 / of_nat d)"
  by sorry


subsection \<open>Mutiplication and ring properties\<close>

instantiation fpxs :: (comm_semiring_1) comm_semiring_1
begin

lift_definition times_fpxs :: "'a fpxs \<Rightarrow> 'a fpxs \<Rightarrow> 'a fpxs" is
  "\<lambda>f g x. (\<Sum>(y,z) | y \<in> supp f \<and> z \<in> supp g \<and> x = y + z. f y * g z)"
proof -
  fix f g :: "rat \<Rightarrow> 'a"
  assume fg: "is_fpxs f" "is_fpxs g"
  show "is_fpxs (\<lambda>x. \<Sum>(y,z) | y \<in> supp f \<and> z \<in> supp g \<and> x = y + z. f y * g z)"
    (is "is_fpxs ?h") unfolding is_fpxs_def
  proof
    from fg obtain bnd1 bnd2 where bnds: "\<forall>x\<in>supp f. x \<ge> bnd1" "\<forall>x\<in>supp g. x \<ge> bnd2"
      by (auto simp: is_fpxs_def bdd_below_def)
    have "supp ?h \<subseteq> (\<lambda>(x,y). x + y) ` (supp f \<times> supp g)"
    proof
      fix x :: rat
      assume "x \<in> supp ?h"
      have "{(y,z). y \<in> supp f \<and> z \<in> supp g \<and> x = y + z} \<noteq> {}"
      proof
        assume eq: "{(y,z). y \<in> supp f \<and> z \<in> supp g \<and> x = y + z} = {}"
        hence "?h x = 0"
          by (simp only:) auto
        with \<open>x \<in> supp ?h\<close> show False by (auto simp: supp_def)
      qed
      thus "x \<in> (\<lambda>(x,y). x + y) ` (supp f \<times> supp g)"
        by auto
    qed
    also have "\<dots> \<subseteq> {bnd1 + bnd2..}"
      using bnds by (auto intro: add_mono)
    finally show "bdd_below (supp ?h)"
      by auto
  next
    define d1 where "d1 = (LCM r\<in>supp f. snd (quotient_of r))"
    define d2 where "d2 = (LCM r\<in>supp g. snd (quotient_of r))"
    have "(LCM r\<in>supp ?h. snd (quotient_of r)) dvd (d1 * d2)"
    proof (intro Lcm_least, safe)
      fix r :: rat
      assume "r \<in> supp ?h"
      hence "(\<Sum>(y, z) | y \<in> supp f \<and> z \<in> supp g \<and> r = y + z. f y * g z) \<noteq> 0"
        by (auto simp: supp_def)
      hence "{(y, z). y \<in> supp f \<and> z \<in> supp g \<and> r = y + z} \<noteq> {}"
        by (intro notI) simp_all
      then obtain y z where yz: "y \<in> supp f" "z \<in> supp g" "r = y + z"
        by auto
      have "snd (quotient_of r) = snd (quotient_of y) * snd (quotient_of z) div
              gcd (fst (quotient_of y) * snd (quotient_of z) +
                   fst (quotient_of z) * snd (quotient_of y))
                  (snd (quotient_of y) * snd (quotient_of z))"
        by (simp add: \<open>r = _\<close> rat_plus_code case_prod_unfold Let_def
                      Rat.normalize_def quotient_of_denom_pos')
      also have "\<dots> dvd snd (quotient_of y) * snd (quotient_of z)"
        by (metis dvd_def dvd_div_mult_self gcd_dvd2)
      also have "\<dots> dvd d1 * d2"
        using yz by (auto simp: d1_def d2_def intro!: mult_dvd_mono)
      finally show "snd (quotient_of r) dvd d1 * d2"
        by (simp add: d1_def d2_def)
    qed
    moreover have "d1 * d2 \<noteq> 0"
      using fg by (auto simp: d1_def d2_def is_fpxs_def)
    ultimately show "(LCM r\<in>supp ?h. snd (quotient_of r)) \<noteq> 0"
      by auto
  qed
qed

lemma fpxs_nth_mult:
  "fpxs_nth (f * g) r =
     (\<Sum>(y,z) | y \<in> fpxs_supp f \<and> z \<in> fpxs_supp g \<and> r = y + z. fpxs_nth f y * fpxs_nth g z)"
  by sorry

lemma fpxs_compose_power_mult [simp]:
  "fpxs_compose_power (f * g) r = fpxs_compose_power f r * fpxs_compose_power g r"
  by sorry

lemma fpxs_supp_of_fls: "fpxs_supp (fpxs_of_fls f) = of_int ` supp (fls_nth f)"
  by sorry

lemma fpxs_of_fls_mult [simp]: "fpxs_of_fls (f * g) = fpxs_of_fls f * fpxs_of_fls g"
  by sorry

instance proof
  show "0 \<noteq> (1 :: 'a fpxs)"
    by transfer (auto simp: fun_eq_iff)
next
  fix f :: "'a fpxs"
  show "1 * f = f"
  proof (transfer, goal_cases)
    case (1 f)
    have "{(y, z). y \<in> supp (\<lambda>r. if r = 0 then (1::'a) else 0) \<and> z \<in> supp f \<and> x = y + z} =
            (if x \<in> supp f then {(0, x)} else {})" for x
      by (auto simp: supp_def split: if_splits)
    thus ?case
      by (auto simp: fun_eq_iff supp_def)
  qed
next
  fix f :: "'a fpxs"
  show "0 * f = 0"
    by transfer (auto simp: fun_eq_iff supp_def)
  show "f * 0 = 0"
    by transfer (auto simp: fun_eq_iff supp_def)
next
  fix f g :: "'a fpxs"
  show "f * g = g * f"
  proof (transfer, rule ext, goal_cases)
    case (1 f g x)
    show "(\<Sum>(y, z)\<in>{(y, z). y \<in> supp f \<and> z \<in> supp g \<and> x = y + z}. f y * g z) =
          (\<Sum>(y, z)\<in>{(y, z). y \<in> supp g \<and> z \<in> supp f \<and> x = y + z}. g y * f z)"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>(x,y). (y,x)" "\<lambda>(x,y). (y,x)"])
         (auto simp: mult_ac)
  qed    
next
  fix f g h :: "'a fpxs"
  define d where "d = (LCM F\<in>{f,g,h}. fpxs_root_order F)"
  have "d > 0"
    by (auto simp: d_def intro!: Nat.gr0I)
  obtain f' where f: "f = fpxs_compose_power (fpxs_of_fls f') (1 / of_nat d)"
    using fpxs_as_fls'[of f d] \<open>d > 0\<close> by (auto simp: d_def)
  obtain g' where g: "g = fpxs_compose_power (fpxs_of_fls g') (1 / of_nat d)"
    using fpxs_as_fls'[of g d] \<open>d > 0\<close> by (auto simp: d_def)
  obtain h' where h: "h = fpxs_compose_power (fpxs_of_fls h') (1 / of_nat d)"
    using fpxs_as_fls'[of h d] \<open>d > 0\<close> by (auto simp: d_def)
  show "(f * g) * h = f * (g * h)"
    by (simp add: f g h mult_ac
             flip: fpxs_compose_power_mult fpxs_compose_power_add fpxs_of_fls_mult)
  show "(f + g) * h = f * h + g * h"
    by (simp add: f g h ring_distribs
             flip: fpxs_compose_power_mult fpxs_compose_power_add fpxs_of_fls_mult fpxs_of_fls_add)
qed

end

instance fpxs :: (comm_ring_1) comm_ring_1
  by intro_classes auto

instance fpxs :: ("{comm_semiring_1,semiring_no_zero_divisors}") semiring_no_zero_divisors
proof
  fix f g :: "'a fpxs"
  assume fg: "f \<noteq> 0" "g \<noteq> 0"
  define d where "d = lcm (fpxs_root_order f) (fpxs_root_order g)"
  have "d > 0"
    by (auto simp: d_def intro!: lcm_pos_nat)
  obtain f' where f: "f = fpxs_compose_power (fpxs_of_fls f') (1 / of_nat d)"
    using fpxs_as_fls'[of f d] \<open>d > 0\<close> by (auto simp: d_def)
  obtain g' where g: "g = fpxs_compose_power (fpxs_of_fls g') (1 / of_nat d)"
    using fpxs_as_fls'[of g d] \<open>d > 0\<close> by (auto simp: d_def)
  show "f * g \<noteq> 0"
    using \<open>d > 0\<close> fg
    by (simp add: f g flip: fpxs_compose_power_mult fpxs_of_fls_mult)
qed

lemma fpxs_of_fls_power [simp]: "fpxs_of_fls (f ^ n) = fpxs_of_fls f ^ n"
  by sorry

lemma fpxs_compose_power_power [simp]:
  "r > 0 \<Longrightarrow> fpxs_compose_power (f ^ n) r = fpxs_compose_power f r ^ n"
  by sorry


subsection \<open>Constant Puiseux series and the series \<open>X\<close>\<close>

lift_definition fpxs_const :: "'a :: zero \<Rightarrow> 'a fpxs" is
  "\<lambda>c n. if n = 0 then c else 0"
proof -
  fix c :: 'a
  have "supp (\<lambda>n::rat. if n = 0 then c else 0) = (if c = 0 then {} else {0})"
    by auto
  thus "is_fpxs (\<lambda>n::rat. if n = 0 then c else 0)"
    unfolding is_fpxs_def by auto
qed

lemma fpxs_const_0 [simp]: "fpxs_const 0 = 0"
  by sorry

lemma fpxs_const_1 [simp]: "fpxs_const 1 = 1"
  by sorry

lemma fpxs_of_fls_const [simp]: "fpxs_of_fls (fls_const c) = fpxs_const c"
  by sorry

lemma fls_of_fpxs_const [simp]: "fls_of_fpxs (fpxs_const c) = fls_const c"
  by sorry

lemma fls_of_fpxs_1 [simp]: "fls_of_fpxs 1 = 1"
  by sorry
  
lift_definition fpxs_X :: "'a :: {one, zero} fpxs" is
  "\<lambda>x. if x = 1 then (1::'a) else 0"
  by (cases "1 = (0 :: 'a)") (auto simp: is_fpxs_def cong: if_cong)

lemma fpxs_const_altdef: "fpxs_const x = fpxs_of_fls (fls_const x)"
  by sorry

lemma fpxs_const_add [simp]: "fpxs_const (x + y) = fpxs_const x + fpxs_const y"
  by sorry

lemma fpxs_const_mult [simp]:
  fixes x y :: "'a::{comm_semiring_1}"
  shows "fpxs_const (x * y) = fpxs_const x * fpxs_const y"
  by sorry

lemma fpxs_const_eq_iff [simp]:
  "fpxs_const x = fpxs_const y \<longleftrightarrow> x = y"
  by sorry

lemma of_nat_fpxs_eq: "of_nat n = fpxs_const (of_nat n)"
  by sorry

lemma fpxs_const_uminus [simp]: "fpxs_const (-x) = -fpxs_const x"
  by sorry

lemma fpxs_const_diff [simp]: "fpxs_const (x - y) = fpxs_const x - fpxs_const y"
  by sorry

lemma of_int_fpxs_eq: "of_int n = fpxs_const (of_int n)"
  by sorry


subsection \<open>More algebraic typeclass instances\<close>

instance fpxs :: ("{comm_semiring_1,semiring_char_0}") semiring_char_0
proof
  show "inj (of_nat :: nat \<Rightarrow> 'a fpxs)"
    by (intro injI) (auto simp: of_nat_fpxs_eq)
qed

instance fpxs :: ("{comm_ring_1,ring_char_0}") ring_char_0 ..

instance fpxs :: (idom) idom ..

instantiation fpxs :: (field) field
begin

definition inverse_fpxs :: "'a fpxs \<Rightarrow> 'a fpxs" where
  "inverse_fpxs f =
     fpxs_compose_power (fpxs_of_fls (inverse (fls_of_fpxs f))) (1 / of_nat (fpxs_root_order f))"

definition divide_fpxs :: "'a fpxs \<Rightarrow> 'a fpxs \<Rightarrow> 'a fpxs" where
  "divide_fpxs f g = f * inverse g"

instance proof
  fix f :: "'a fpxs"
  assume "f \<noteq> 0"
  define f' where "f' = fls_of_fpxs f"
  define d where "d = fpxs_root_order f"
  have "d > 0" by (auto simp: d_def)
  have f: "f = fpxs_compose_power (fpxs_of_fls f') (1 / of_nat d)"
    by (simp add: f'_def d_def fpxs_as_fls)

  have "inverse f * f = fpxs_compose_power (fpxs_of_fls (inverse f')) (1 / of_nat d) * f"
    by (simp add: inverse_fpxs_def f'_def d_def)
  also have "fpxs_compose_power (fpxs_of_fls (inverse f')) (1 / of_nat d) * f =
             fpxs_compose_power (fpxs_of_fls (inverse f' * f')) (1 / of_nat d)"
    by (simp add: f)
  also have "inverse f' * f' = 1"
    using \<open>f \<noteq> 0\<close> \<open>d > 0\<close> by (simp add: f field_simps)
  finally show "inverse f * f = 1"
    using \<open>d > 0\<close> by simp
qed (auto simp: divide_fpxs_def inverse_fpxs_def)

end

instance fpxs :: (field_char_0) field_char_0 ..


subsection \<open>Valuation\<close>

definition fpxs_val :: "'a :: zero fpxs \<Rightarrow> rat" where
  "fpxs_val f =
     of_int (fls_subdegree (fls_of_fpxs f)) / rat_of_nat (fpxs_root_order f)"

lemma fpxs_val_of_fls [simp]: "fpxs_val (fpxs_of_fls f) = of_int (fls_subdegree f)"
  by sorry

lemma fpxs_nth_compose_power [simp]:
  assumes "r > 0"
  shows   "fpxs_nth (fpxs_compose_power f r) n = fpxs_nth f (n / r)"
  by sorry

lemma fls_of_fpxs_uminus [simp]: "fls_of_fpxs (-f) = -fls_of_fpxs f"
  by sorry

lemma fpxs_root_order_uminus [simp]: "fpxs_root_order (-f) = fpxs_root_order f"
  by sorry

lemma fpxs_val_uminus [simp]: "fpxs_val (-f) = fpxs_val f"
  by sorry

lemma fpxs_val_minus_commute: "fpxs_val (f - g) = fpxs_val (g - f)"
  by sorry

lemma fpxs_val_const [simp]: "fpxs_val (fpxs_const c) = 0"
  by sorry

lemma fpxs_val_1 [simp]: "fpxs_val 1 = 0"
  by sorry

lemma of_int_fls_subdegree_of_fpxs:
  "rat_of_int (fls_subdegree (fls_of_fpxs f)) = fpxs_val f * of_nat (fpxs_root_order f)"
  by sorry

lemma fpxs_nth_val_nonzero: 
  assumes "f \<noteq> 0"
  shows   "fpxs_nth f (fpxs_val f) \<noteq> 0"
  by sorry

lemma fpxs_nth_below_val:
  assumes n: "n < fpxs_val f"
  shows   "fpxs_nth f n = 0"
  by sorry

lemma fpxs_val_leI: "fpxs_nth f r \<noteq> 0 \<Longrightarrow> fpxs_val f \<le> r"
  by sorry

lemma fpxs_val_0 [simp]: "fpxs_val 0 = 0"
  by sorry

lemma fpxs_val_geI: 
  assumes "f \<noteq> 0" "\<And>r. r < r' \<Longrightarrow> fpxs_nth f r = 0"
  shows   "fpxs_val f \<ge> r'"
  by sorry

lemma fpxs_val_compose_power [simp]:
  assumes "r > 0"
  shows   "fpxs_val (fpxs_compose_power f r) = fpxs_val f * r"
  by sorry

lemma fpxs_val_add_ge:
  assumes "f + g \<noteq> 0"
  shows   "fpxs_val (f + g) \<ge> min (fpxs_val f) (fpxs_val g)"
  by sorry

lemma fpxs_val_diff_ge:
  assumes "f \<noteq> g"
  shows   "fpxs_val (f - g) \<ge> min (fpxs_val f) (fpxs_val g)"
  by sorry

lemma fpxs_nth_mult_val:
  "fpxs_nth (f * g) (fpxs_val f + fpxs_val g) = fpxs_nth f (fpxs_val f) * fpxs_nth g (fpxs_val g)"
  by sorry

lemma fpxs_val_mult [simp]:
  fixes f g :: "'a :: {comm_semiring_1, semiring_no_zero_divisors} fpxs"
  assumes "f \<noteq> 0" "g \<noteq> 0"
  shows "fpxs_val (f * g) = fpxs_val f + fpxs_val g"
  by sorry

lemma fpxs_val_power [simp]:
  fixes f :: "'a :: {comm_semiring_1, semiring_no_zero_divisors} fpxs"
  assumes "f \<noteq> 0 \<or> n > 0"
  shows "fpxs_val (f ^ n) = of_nat n * fpxs_val f"
  by sorry

lemma fpxs_nth_power_val [simp]:
  fixes f :: "'a :: {comm_semiring_1, semiring_no_zero_divisors} fpxs"
  shows "fpxs_nth (f ^ r) (rat_of_nat r * fpxs_val f) = fpxs_nth f (fpxs_val f) ^ r"
  by sorry


subsection \<open>Powers of \<open>X\<close> and shifting\<close>

lift_definition fpxs_X_power :: "rat \<Rightarrow> 'a :: {zero, one} fpxs" is
  "\<lambda>r n :: rat. if n = r then 1 else (0 :: 'a)"
proof -
  fix r :: rat
  have "supp (\<lambda>n. if n = r then 1 else (0 :: 'a)) = (if (1 :: 'a) = 0 then {} else {r})"
    by (auto simp: supp_def)
  thus "is_fpxs (\<lambda>n. if n = r then 1 else (0 :: 'a))"
    using quotient_of_denom_pos'[of r] by (auto simp: is_fpxs_def)
qed

lemma fpxs_X_power_0 [simp]: "fpxs_X_power 0 = 1"
  by sorry

lemma fpxs_X_power_add: "fpxs_X_power (a + b) = fpxs_X_power a * fpxs_X_power b"
  by sorry

lemma fpxs_X_power_mult: "fpxs_X_power (rat_of_nat n * m) = fpxs_X_power m ^ n"
  by sorry

lemma fpxs_of_fls_X_power [simp]: "fpxs_of_fls (fls_shift n 1) = fpxs_X_power (-rat_of_int n)"
  by sorry

lemma fpxs_X_power_neq_0 [simp]: "fpxs_X_power r \<noteq> (0 :: 'a :: zero_neq_one fpxs)"
  by sorry

lemma fpxs_X_power_eq_1_iff [simp]: "fpxs_X_power r = (1 :: 'a :: zero_neq_one fpxs) \<longleftrightarrow> r = 0"
  by sorry


lift_definition fpxs_shift :: "rat \<Rightarrow> 'a :: zero fpxs \<Rightarrow> 'a fpxs" is
  "\<lambda>r f n. f (n + r)"
proof -
  fix r :: rat and f :: "rat \<Rightarrow> 'a"
  assume f: "is_fpxs f"
  have subset: "supp (\<lambda>n. f (n + r)) \<subseteq> (\<lambda>n. n + r) -` supp f"
    by (auto simp: supp_def)
  have eq: "(\<lambda>n. n + r) -` supp f = (\<lambda>n. n - r) ` supp f"
    by (auto simp: image_iff algebra_simps)

  show "is_fpxs (\<lambda>n. f (n + r))"
    unfolding is_fpxs_def
  proof
    have "bdd_below ((\<lambda>n. n + r) -` supp f)"
      unfolding eq by (rule bdd_below_image_mono) (use f in \<open>auto simp: is_fpxs_def mono_def\<close>)
    thus "bdd_below (supp (\<lambda>n. f (n + r)))"
      by (rule bdd_below_mono[OF _ subset])
  next
    have "(LCM r\<in>supp (\<lambda>n. f (n + r)). snd (quotient_of r)) dvd
          (LCM r\<in>(\<lambda>n. n + r) -` supp f. snd (quotient_of r))"
      by (intro Lcm_subset image_mono subset)
    also have "\<dots> = (LCM x\<in>supp f. snd (quotient_of (x - r)))"
      by (simp only: eq image_image o_def)
    also have "\<dots> dvd (LCM x\<in>supp f. snd (quotient_of r) * snd (quotient_of x))"
      by (subst mult.commute, intro Lcm_mono quotient_of_denom_diff_dvd)
    also have "\<dots> = Lcm ((\<lambda>x. snd (quotient_of r) * x) ` (\<lambda>x. snd (quotient_of x)) ` supp f)"
      by (simp add: image_image o_def)
    also have "\<dots> dvd normalize (snd (quotient_of r) * (LCM x\<in>supp f. snd (quotient_of x)))"
    proof (cases "supp f = {}")
      case False
      thus ?thesis by (subst Lcm_mult) auto
    qed auto
    finally show "(LCM r\<in>supp (\<lambda>n. f (n + r)). snd (quotient_of r)) \<noteq> 0"
      using quotient_of_denom_pos'[of r] f by (auto simp: is_fpxs_def)
  qed
qed

lemma fpxs_nth_shift [simp]: "fpxs_nth (fpxs_shift r f) n = fpxs_nth f (n + r)"
  by sorry

lemma fpxs_shift_0_left [simp]: "fpxs_shift 0 f = f"
  by sorry

lemma fpxs_shift_add_left: "fpxs_shift (m + n) f = fpxs_shift m (fpxs_shift n f)"
  by sorry

lemma fpxs_shift_diff_left: "fpxs_shift (m - n) f = fpxs_shift m (fpxs_shift (-n) f)"
  by sorry

lemma fpxs_shift_0 [simp]: "fpxs_shift r 0 = 0"
  by sorry

lemma fpxs_shift_add [simp]: "fpxs_shift r (f + g) = fpxs_shift r f + fpxs_shift r g"
  by sorry

lemma fpxs_shift_uminus [simp]: "fpxs_shift r (-f) = -fpxs_shift r f"
  by sorry

lemma fpxs_shift_shift_uminus [simp]: "fpxs_shift r (fpxs_shift (-r) f) = f"
  by sorry

lemma fpxs_shift_shift_uminus' [simp]: "fpxs_shift (-r) (fpxs_shift r f) = f"
  by sorry

lemma fpxs_shift_diff [simp]: "fpxs_shift r (f - g) = fpxs_shift r f - fpxs_shift r g"
  by sorry

lemma fpxs_shift_compose_power [simp]:
  "fpxs_shift r (fpxs_compose_power f s) = fpxs_compose_power (fpxs_shift (r / s) f) s"
  by sorry

lemma rat_of_int_div_dvd: "d dvd n \<Longrightarrow> rat_of_int (n div d) = rat_of_int n / rat_of_int d"
  by sorry

lemma fpxs_of_fls_shift [simp]:
  "fpxs_of_fls (fls_shift n f) = fpxs_shift (of_int n) (fpxs_of_fls f)"
  by sorry

lemma fpxs_shift_mult: "f * fpxs_shift r g = fpxs_shift r (f * g)"
                       "fpxs_shift r f * g = fpxs_shift r (f * g)"
  by sorry

lemma fpxs_shift_1: "fpxs_shift r 1 = fpxs_X_power (-r)"
  by sorry

lemma fpxs_X_power_conv_shift: "fpxs_X_power r = fpxs_shift (-r) 1"
  by sorry

lemma fpxs_shift_power [simp]: "fpxs_shift n x ^ m = fpxs_shift (of_nat m * n) (x ^ m)"
  by sorry

lemma fpxs_compose_power_X_power [simp]:
  "s > 0 \<Longrightarrow> fpxs_compose_power (fpxs_X_power r) s = fpxs_X_power (r * s)"
  by sorry


subsection \<open>The \<open>n\<close>-th root of a Puiseux series\<close>

text \<open>
  In this section, we define the formal root of a Puiseux series. This is done using the
  same concept for formal power series. There is still one interesting theorems that is missing
  here, e.g.\ the uniqueness (which could probably be lifted over from FPSs) somehow.
\<close>

definition fpxs_radical :: "(nat \<Rightarrow> 'a :: field_char_0 \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a fpxs \<Rightarrow> 'a fpxs" where
  "fpxs_radical rt r f = (if f = 0 then 0 else
     (let f' = fls_base_factor_to_fps (fls_of_fpxs f);
          f'' = fpxs_of_fls (fps_to_fls (fps_radical rt r f'))
      in  fpxs_shift (-fpxs_val f / rat_of_nat r)
            (fpxs_compose_power f'' (1 / rat_of_nat (fpxs_root_order f)))))"

lemma fpxs_radical_0 [simp]: "fpxs_radical rt r 0 = 0"
  by sorry

lemma 
  fixes r :: nat
  assumes r: "r > 0"
  shows fpxs_power_radical:
        "rt r (fpxs_nth f (fpxs_val f)) ^ r = fpxs_nth f (fpxs_val f) \<Longrightarrow> fpxs_radical rt r f ^ r = f"
    and fpxs_radical_lead_coeff:
          "f \<noteq> 0 \<Longrightarrow> fpxs_nth (fpxs_radical rt r f) (fpxs_val f / rat_of_nat r) =
                       rt r (fpxs_nth f (fpxs_val f))"
  by sorry

lemma fls_base_factor_power:
  fixes f :: "'a::{semiring_1, semiring_no_zero_divisors} fls"
  shows "fls_base_factor (f ^ n) = fls_base_factor f ^ n"
  by sorry

(* TODO: Uniqueness of radical. Also: composition and composition inverse *)

hide_const (open) supp


subsection \<open>Algebraic closedness\<close>

text \<open>
  We will now show that the field of formal Puiseux series over an algebraically closed field of
  characteristic 0 is again algebraically closed.

  The typeclass constraint \<^class>\<open>field_gcd\<close> is a technical constraint that mandates that
  the field has a (trivial) GCD operation defined on it. It comes from some peculiarities of
  Isabelle's typeclass system and can be considered unimportant, since any concrete type of
  class \<^class>\<open>field\<close> can easily be made an instance of \<^class>\<open>field_gcd\<close>.

  It would be possible to get rid of this constraint entirely here, but it is not worth
  the effort.

  The proof is a fairly standard one that uses Hensel's lemma. Some preliminary tricks are
  required to be able to use it, however, namely a number of non-obvious changes of variables
  to turn the polynomial with Puiseux coefficients into one with formal power series coefficients.
  The overall approach was taken from an article by Nowak~\<^cite>\<open>"nowak2000"\<close>.

  Basically, what we need to show is this: Let 
  \[p(X,Z) = a_n(Z) X^n + a_{n-1}(Z) X^{n-1} + \ldots + a_0(Z)\]
  be a polynomial in \<open>X\<close> of degree at least 2
  with coefficients that are formal Puiseux series in \<open>Z\<close>. Then \<open>p\<close> is reducible, i.e. it splits
  into two non-constant factors.

  Due to work we have already done elsewhere, we may assume here that $a_n = 1$, $a_{n-1} = 0$, and
  $a_0 \neq 0$, all of which will come in very useful.
\<close>

instance fpxs :: ("{alg_closed_field, field_char_0, field_gcd}") alg_closed_field
proof (rule alg_closedI_reducible_coeff_deg_minus_one_eq_0)
  fix p :: "'a fpxs poly"
  assume deg_p: "degree p > 1"  and lc_p: "lead_coeff p = 1"
  assume coeff_deg_minus_1: "coeff p (degree p - 1) = 0"
  assume "coeff p 0 \<noteq> 0"
  define N where "N = degree p"

  text \<open>
    Let $a_0, \ldots, a_n$ be the coefficients of \<open>p\<close> with $a_n = 1$. Now let \<open>r\<close> be the maximum of
    $-\frac{\text{val}(a_i)}{n-i}$ ranging over all $i < n$ such that $a_i \neq 0$.
  \<close>
  define r :: rat
    where "r = (MAX i\<in>{i\<in>{..<N}. coeff p i \<noteq> 0}.
                  -fpxs_val (poly.coeff p i) / (rat_of_nat N - rat_of_nat i))"

  text \<open>
    We write $r = a / b$ such that all the $a_i$ can be written as Laurent series in
    $X^{1/b}$, i.e. the root orders of all the $a_i$ divide $b$:
  \<close>
  obtain a b where ab: "b > 0" "r = of_int a / of_nat b" "\<forall>i\<le>N. fpxs_root_order (coeff p i) dvd b"
  proof -
    define b where "b = lcm (nat (snd (quotient_of r))) (LCM i\<in>{..N}. fpxs_root_order (coeff p i))"
    define x where "x = b div nat (snd (quotient_of r))"
    define a where "a = fst (quotient_of r) * int x"

    show ?thesis
    proof (rule that)
      show "b > 0"
        using quotient_of_denom_pos'[of r] by (auto simp: b_def intro!: Nat.gr0I)
      have b_eq: "b = nat (snd (quotient_of r)) * x"
        by (simp add: x_def b_def)
      have "x > 0"
        using b_eq \<open>b > 0\<close> by (auto intro!: Nat.gr0I)
      have "r = rat_of_int (fst (quotient_of r)) / rat_of_int (int (nat (snd (quotient_of r))))"
        using quotient_of_denom_pos'[of r] quotient_of_div[of r] by simp
      also have "\<dots> = rat_of_int a / rat_of_nat b"
        using \<open>x > 0\<close> by (simp add: a_def b_eq)
      finally show "r = rat_of_int a / rat_of_nat b" .
      show "\<forall>i\<le>N. fpxs_root_order (poly.coeff p i) dvd b"
        by (auto simp: b_def)
    qed
  qed

  text \<open>
    We write all the coefficients of \<open>p\<close> as Laurent series in $X^{1/b}$:
  \<close>
  have "\<exists>c. coeff p i = fpxs_compose_power (fpxs_of_fls c) (1 / rat_of_nat b)" if i: "i \<le> N" for i
  proof -
    have "fpxs_root_order (coeff p i) dvd b"
      using ab(3) i by auto
    from fpxs_as_fls'[OF this \<open>b > 0\<close>] show ?thesis by metis
  qed
  then obtain c_aux where c_aux:
    "coeff p i = fpxs_compose_power (fpxs_of_fls (c_aux i)) (1 / rat_of_nat b)" if "i \<le> N" for i
    by metis
  define c where "c = (\<lambda>i. if i \<le> N then c_aux i else 0)"
  have c: "coeff p i = fpxs_compose_power (fpxs_of_fls (c i)) (1 / rat_of_nat b)" for i
    using c_aux[of i] by (auto simp: c_def N_def coeff_eq_0)
  have c_eq_0 [simp]: "c i = 0" if "i > N" for i
    using that by (auto simp: c_def)
  have c_eq: "fpxs_of_fls (c i) = fpxs_compose_power (coeff p i) (rat_of_nat b)" for i
    using c[of i] \<open>b > 0\<close> by (simp add: fpxs_compose_power_distrib)

  text \<open>
    We perform another change of variables and multiply with a suitable power of \<open>X\<close> to turn our
    Laurent coefficients into FPS coefficients:
  \<close>
  define c' where "c' = (\<lambda>i. fls_X_intpow ((int N - int i) * a) * c i)"
  have "c' N = 1"
    using c[of N] \<open>lead_coeff p = 1\<close> \<open>b > 0\<close> by (simp add: c'_def N_def)

  have subdegree_c: "of_int (fls_subdegree (c i)) = fpxs_val (coeff p i) * rat_of_nat b"
    if i: "i \<le> N" for i
  proof -
    have "rat_of_int (fls_subdegree (c i)) = fpxs_val (fpxs_of_fls (c i))"
      by simp
    also have "fpxs_of_fls (c i) = fpxs_compose_power (poly.coeff p i) (rat_of_nat b)"
      by (subst c_eq) auto
    also have "fpxs_val \<dots> = fpxs_val (coeff p i) * rat_of_nat b"
      using \<open>b > 0\<close> by simp
    finally show ?thesis .
  qed

  text \<open>
    We now write all the coefficients as FPSs:
  \<close>
  have "\<exists>c''. c' i = fps_to_fls c''" if "i \<le> N" for i
  proof (cases "i = N")
    case True
    hence "c' i = fps_to_fls 1"
      using \<open>c' N = 1\<close> by simp
    thus ?thesis by metis
  next
    case i: False
    show ?thesis
    proof (cases "c i = 0")
      case True
      hence "c' i = 0" by (auto simp: c'_def)
      thus ?thesis
        by (metis fps_zero_to_fls)
    next
      case False
      hence "coeff p i \<noteq> 0"
        using c_eq[of i] by auto
      hence r_ge: "r \<ge> -fpxs_val (poly.coeff p i) / (rat_of_nat N - rat_of_nat i)"
        unfolding r_def using i that False by (intro Max.coboundedI) auto

      have "fls_subdegree (c' i) = fls_subdegree (c i) + (int N - int i) * a"
        using i that False by (simp add: c'_def fls_X_intpow_times_conv_shift subdegree_c)
      also have "rat_of_int \<dots> =
                   fpxs_val (poly.coeff p i) * of_nat b + (of_nat N - of_nat i) * of_int a"
        using i that False by (simp add: subdegree_c)
      also have "\<dots> = of_nat b * (of_nat N - of_nat i) *
                        (fpxs_val (poly.coeff p i) / (of_nat N - of_nat i) + r)"
        using \<open>b > 0\<close> i by (auto simp: field_simps ab(2))
      also have "\<dots> \<ge> 0"
        using r_ge that by (intro mult_nonneg_nonneg) auto
      finally have "fls_subdegree (c' i) \<ge> 0" by simp
      hence "\<exists>c''. c' i = fls_shift 0 (fps_to_fls c'')"
        by (intro fls_as_fps') (auto simp: algebra_simps)
      thus ?thesis by simp
    qed
  qed
  then obtain c''_aux where c''_aux: "c' i = fps_to_fls (c''_aux i)" if "i \<le> N" for i
    by metis
  define c'' where "c'' = (\<lambda>i. if i \<le> N then c''_aux i else 0)"
  have c': "c' i = fps_to_fls (c'' i)" for i
  proof (cases "i \<le> N")
    case False
    thus ?thesis by (auto simp: c'_def c''_def)
  qed (auto simp: c''_def c''_aux)
  have c''_eq: "fps_to_fls (c'' i) = c' i" for i
    using c'[of i] by simp

  define p' where "p' = Abs_poly c''"
  have coeff_p': "coeff p' = c''"
    unfolding p'_def
  proof (rule coeff_Abs_poly)
    fix i assume "i > N"
    hence "coeff p i = 0"
      by (simp add: N_def coeff_eq_0)
    thus "c'' i = 0" using c'[of i] c[of i] \<open>b > 0\<close> \<open>N < i\<close> c''_def by auto
  qed

  text \<open>
    We set up some homomorphisms to convert between the two polynomials:
  \<close>
  interpret comppow: map_poly_inj_idom_hom "(\<lambda>x::'a fpxs. fpxs_compose_power x (1/rat_of_nat b))"
    by unfold_locales (use \<open>b > 0\<close> in simp_all)
  define lift_poly :: "'a fps poly \<Rightarrow> 'a fpxs poly" where
    "lift_poly = (\<lambda>p. pcompose p [:0, fpxs_X_power r:]) \<circ>
                  (map_poly ((\<lambda>x. fpxs_compose_power x (1/rat_of_nat b)) \<circ> fpxs_of_fls \<circ> fps_to_fls))"
  have [simp]: "degree (lift_poly q) = degree q" for q
    unfolding lift_poly_def by (simp add: degree_map_poly)
  
  interpret fps_to_fls: map_poly_inj_idom_hom fps_to_fls
    by unfold_locales (simp_all add: fls_times_fps_to_fls)
  interpret fpxs_of_fls: map_poly_inj_idom_hom fpxs_of_fls
    by unfold_locales simp_all
  interpret lift_poly: inj_idom_hom lift_poly
    unfolding lift_poly_def
    by (intro inj_idom_hom_compose inj_idom_hom_pcompose inj_idom_hom.inj_idom_hom_map_poly
              fps_to_fls.base.inj_idom_hom_axioms fpxs_of_fls.base.inj_idom_hom_axioms
              comppow.base.inj_idom_hom_axioms) simp_all
  interpret lift_poly: map_poly_inj_idom_hom lift_poly
    by unfold_locales

  define C :: "'a fpxs" where "C = fpxs_X_power (- (rat_of_nat N * r))"
  have [simp]: "C \<noteq> 0"
    by (auto simp: C_def)

  text \<open>
    Now, finally: the original polynomial and the new polynomial are related through the
    \<^term>\<open>lift_poly\<close> homomorphism:
  \<close>
  have p_eq: "p = smult C (lift_poly p')"
    using \<open>b > 0\<close>
    by (intro poly_eqI)
       (simp_all add: coeff_map_poly coeff_pcompose_linear coeff_p' c c''_eq c'_def C_def
                      ring_distribs fpxs_X_power_conv_shift fpxs_shift_mult lift_poly_def ab(2)
                 flip: fpxs_X_power_add fpxs_X_power_mult fpxs_shift_add_left)
  have [simp]: "degree p' = N"
    unfolding N_def using \<open>b > 0\<close> by (simp add: p_eq)
  have lc_p': "lead_coeff p' = 1"
    using c''_eq[of N] by (simp add: coeff_p' \<open>c' N = 1\<close>)
  have "coeff p' (N - 1) = 0"
    using coeff_deg_minus_1 \<open>b > 0\<close> unfolding N_def [symmetric]
    by (simp add: p_eq lift_poly_def coeff_map_poly coeff_pcompose_linear)

  text \<open>
    We reduce $p'(X,Z)$ to $p'(X,0)$:
  \<close>
  define p'_proj where "p'_proj = reduce_fps_poly p'"
  have [simp]: "degree p'_proj = N"
    unfolding p'_proj_def using lc_p' by (subst degree_reduce_fps_poly_monic) simp_all
  have lc_p'_proj: "lead_coeff p'_proj = 1"
    unfolding p'_proj_def using lc_p' by (subst reduce_fps_poly_monic) simp_all
  hence [simp]: "p'_proj \<noteq> 0"
    by auto
  have "coeff p'_proj (N - 1) = 0"
    using \<open>coeff p' (N - 1) = 0\<close> by (simp add: p'_proj_def reduce_fps_poly_def)

  text \<open>
    We now show that \<^term>\<open>p'_proj\<close> splits into non-trivial coprime factors. To do this, we
    have to show that it has two distinct roots, i.e. that it is not of the form $(X - c)^n$.
  \<close>
  obtain g h where gh: "degree g > 0" "degree h > 0" "coprime g h" "p'_proj = g * h"
  proof -
    have "degree p'_proj > 1"
      using deg_p by (auto simp: N_def)
    text \<open>Let \<open>x\<close> be an arbitrary root of \<^term>\<open>p'_proj\<close>:\<close>
    then obtain x where x: "poly p'_proj x = 0"
      using alg_closed_imp_poly_has_root[of p'_proj] by force

    text \<open>Assume for the sake of contradiction that \<^term>\<open>p'_proj\<close> were equal to $(1-x)^n$:\<close>
    have not_only_one_root: "p'_proj \<noteq> [:-x, 1:] ^ N"
    proof safe
      assume *: "p'_proj = [:-x, 1:] ^ N"

      text \<open>
        If \<open>x\<close> were non-zero, all the coefficients of \<open>p'_proj\<close> would also be non-zero by the
        Binomial Theorem. Since we know that the coefficient of \<open>n - 1\<close> \<^emph>\<open>is\<close> zero, this means
        that \<open>x\<close> must be zero:
      \<close>
      have "coeff p'_proj (N - 1) = 0" by fact
      hence "x = 0"
        by (subst (asm) *, subst (asm) coeff_linear_poly_power) auto

      text \<open>
        However, by our choice of \<open>r\<close>, we know that there is an index \<open>i\<close> such that \<open>c' i\<close> has
        is non-zero and has valuation (i.e. subdegree) 0, which means that the \<open>i\<close>-th coefficient
        of \<^term>\<open>p'_proj\<close> must also be non-zero.
      \<close>
      have "0 < N \<and> coeff p 0 \<noteq> 0"
        using deg_p \<open>coeff p 0 \<noteq> 0\<close> by (auto simp: N_def)
      hence "{i\<in>{..<N}. coeff p i \<noteq> 0} \<noteq> {}"
        by blast
      hence "r \<in> (\<lambda>i. -fpxs_val (poly.coeff p i) / (rat_of_nat N - rat_of_nat i)) `
              {i\<in>{..<N}. coeff p i \<noteq> 0}"
        unfolding r_def using deg_p by (intro Max_in) (auto simp: N_def)
      then obtain i where i: "i < N" "coeff p i \<noteq> 0"
                             "-fpxs_val (coeff p i) / (rat_of_nat N - rat_of_nat i) = r"
        by blast
      hence [simp]: "c' i \<noteq> 0"
        using i c[of i] by (auto simp: c'_def)
      have "fpxs_val (poly.coeff p i) = rat_of_int (fls_subdegree (c i)) / rat_of_nat b"
        using subdegree_c[of i] i \<open>b > 0\<close> by (simp add: field_simps)
      also have "fpxs_val (coeff p i) = -r * (rat_of_nat N - rat_of_nat i)"
        using i by (simp add: field_simps)
      finally have "rat_of_int (fls_subdegree (c i)) = - r * (of_nat N - of_nat i) * of_nat b"
        using \<open>b > 0\<close> by (simp add: field_simps)
      also have "c i = fls_shift ((int N - int i) * a) (c' i)"
        using i by (simp add: c'_def ring_distribs fls_X_intpow_times_conv_shift
                         flip: fls_shifted_times_simps(2))
      also have "fls_subdegree \<dots> = fls_subdegree (c' i) - (int N - int i) * a"
        by (subst fls_shift_subdegree) auto
      finally have "fls_subdegree (c' i) = 0"
        using \<open>b > 0\<close> by (simp add: ab(2))
      hence "subdegree (coeff p' i) = 0"
        by (simp flip: c''_eq add: fls_subdegree_fls_to_fps coeff_p')
      moreover have "coeff p' i \<noteq> 0"
        using \<open>c' i \<noteq> 0\<close> c' coeff_p' by auto
      ultimately have "coeff p' i $ 0 \<noteq> 0"
        using subdegree_eq_0_iff by blast

      also have "coeff p' i $ 0 = coeff p'_proj i"
        by (simp add: p'_proj_def reduce_fps_poly_def)
      also have "\<dots> = 0"
        by (subst *, subst coeff_linear_poly_power) (use i \<open>x = 0\<close> in auto)
      finally show False by simp
    qed

    text \<open>
      We can thus obtain our second root \<open>y\<close> from the factorisation:
    \<close>
    have "\<exists>y. x \<noteq> y \<and> poly p'_proj y = 0"
    proof (rule ccontr)
      assume *: "\<not>(\<exists>y. x \<noteq> y \<and> poly p'_proj y = 0)"
      have "p'_proj \<noteq> 0" by simp
      then obtain A where A: "size A = degree p'_proj"
                             "p'_proj = smult (lead_coeff p'_proj) (\<Prod>x\<in>#A. [:-x, 1:])"
        using alg_closed_imp_factorization[of p'_proj] by blast
      have "set_mset A = {x. poly p'_proj x = 0}"
        using lc_p'_proj by (subst A) (auto simp: poly_prod_mset)
      also have "\<dots> = {x}"
        using x * by auto
      finally have "A = replicate_mset N x"
        using set_mset_subset_singletonD[of A x] A(1) by simp
      with A(2) have "p'_proj = [:- x, 1:] ^ N"
        using lc_p'_proj by simp
      with not_only_one_root show False 
        by contradiction
    qed
    then obtain y where "x \<noteq> y" "poly p'_proj y = 0"
      by blast

    text \<open>
      It now follows easily that \<^term>\<open>p'_proj\<close> splits into non-trivial and coprime factors:
    \<close>
    show ?thesis
    proof (rule alg_closed_imp_poly_splits_coprime)
      show "degree p'_proj > 1"
        using deg_p by (simp add: N_def)
      show "x \<noteq> y" "poly p'_proj x = 0" "poly p'_proj y = 0"
        by fact+
    qed (use that in metis)
  qed

  text \<open>
    By Hensel's lemma, these factors give rise to corresponding factors of \<open>p'\<close>:
  \<close>
  interpret hensel: fps_hensel p' p'_proj g h
  proof unfold_locales
    show "lead_coeff p' = 1"
      using lc_p' by simp
  qed (use gh \<open>coprime g h\<close> in \<open>simp_all add: p'_proj_def\<close>) 

  text \<open>All that remains now is to undo the variable substitutions we did above:\<close>
  have "p = [:C:] * lift_poly hensel.G * lift_poly hensel.H"
    unfolding p_eq by (subst hensel.F_splits) (simp add: hom_distribs)
  thus "\<not>irreducible p"
    by (rule reducible_polyI) (use hensel.deg_G hensel.deg_H gh in simp_all)
qed

text \<open>
  We do not actually show that this is the algebraic closure since this cannot be stated
  idiomatically in the typeclass setting and is probably not very useful either, but it can
  be motivated like this:

  Suppose we have an algebraically closed extension $L$ of the field of Laurent series. Clearly,
  $X^{a/b}\in L$ for any integer \<open>a\<close> and any positive integer \<open>b\<close> since
  $(X^{a/b})^b - X^a = 0$. But any Puiseux series $F(X)$ with root order \<open>b\<close> can
  be written as
  \[F(X) = \sum_{k=0}^{b-1} X^{k/b} F_k(X)\]
  where the Laurent series $F_k(X)$ are defined as follows:
  \[F_k(X) := \sum_{n = n_{0,k}}^\infty [X^{n + k/b}] F(X) X^n\]
  Thus, $F(X)$ can be written as a finite sum of products of elements in $L$ and must therefore
  also be in $L$. Thus, the Puiseux series are all contained in $L$.
\<close>


subsection \<open>Metric and topology\<close>

text \<open>
  Formal Puiseux series form a metric space with the usual metric for formal series:
  Two series are ``close'' to one another if they have many initial coefficients in common.
\<close>

instantiation fpxs :: (zero) norm
begin

definition norm_fpxs :: "'a fpxs \<Rightarrow> real" where
  "norm f = (if f = 0 then 0 else 2 powr (-of_rat (fpxs_val f)))"

instance ..

end


instantiation fpxs :: (group_add) dist
begin

definition dist_fpxs :: "'a fpxs \<Rightarrow> 'a fpxs \<Rightarrow> real" where
  "dist f g = (if f = g then 0 else 2 powr (-of_rat (fpxs_val (f - g))))"

instance ..

end


instantiation fpxs :: (group_add) metric_space
begin

definition uniformity_fpxs_def:
  "(uniformity :: ('a fpxs \<times> 'a fpxs) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_fpxs_def:
  "open (U :: 'a fpxs set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance proof
  fix f g h :: "'a fpxs"
  show "dist f g \<le> dist f h + dist g h"
  proof (cases "f \<noteq> g \<and> f \<noteq> h \<and> g \<noteq> h")
    case True
    have "dist f g \<le> 2 powr -real_of_rat (min (fpxs_val (f - h)) (fpxs_val (g - h)))"
      using fpxs_val_add_ge[of "f - h" "h - g"] True
      by (auto simp: algebra_simps fpxs_val_minus_commute dist_fpxs_def of_rat_less_eq)
    also have "\<dots> \<le> dist f h + dist g h"
      using True by (simp add: dist_fpxs_def min_def)
    finally show ?thesis .
  qed (auto simp: dist_fpxs_def fpxs_val_minus_commute)
qed (simp_all add: uniformity_fpxs_def open_fpxs_def dist_fpxs_def)

end


instance fpxs :: (group_add) dist_norm
  by standard (auto simp: dist_fpxs_def norm_fpxs_def)

lemma fpxs_const_eq_0_iff [simp]: "fpxs_const x = 0 \<longleftrightarrow> x = 0"
  by sorry

lemma semiring_char_fpxs [simp]: "CHAR('a :: comm_semiring_1 fpxs) = CHAR('a)"
  by sorry

instance fpxs :: ("{semiring_prime_char,comm_semiring_1}") semiring_prime_char
  by (rule semiring_prime_charI) auto
instance fpxs :: ("{comm_semiring_prime_char,comm_semiring_1}") comm_semiring_prime_char
  by standard
instance fpxs :: ("{comm_ring_prime_char,comm_semiring_1}") comm_ring_prime_char
  by standard
instance fpxs :: ("{idom_prime_char,comm_semiring_1}") idom_prime_char
  by standard
instance fpxs :: ("field_prime_char") field_prime_char
  by standard auto

end