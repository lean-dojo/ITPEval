(*  Title:      HOL/Computational_Algebra/Primes.thy
    Author:     Christophe Tabacznyj
    Author:     Lawrence C. Paulson
    Author:     Amine Chaieb
    Author:     Thomas M. Rasmussen
    Author:     Jeremy Avigad
    Author:     Tobias Nipkow
    Author:     Manuel Eberl

This theory deals with properties of primes. Definitions and lemmas are
proved uniformly for the natural numbers and integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on @{cite davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD". IntPrimes also defined and developed
the congruence relations on the integers. The notion was extended to
the natural numbers by Chaieb.

Jeremy Avigad combined all of these, made everything uniform for the
natural numbers and the integers, and added a number of new theorems.

Tobias Nipkow cleaned up a lot.

Florian Haftmann and Manuel Eberl put primality and prime factorisation
onto an algebraic foundation and thus generalised these concepts to 
other rings, such as polynomials. (see also the Factorial_Ring theory).

There were also previous formalisations of unique factorisation by 
Thomas Marthedal Rasmussen, Jeremy Avigad, and David Gray.
*)

section \<open>Primes\<close>

theory Primes
imports Euclidean_Algorithm
begin

subsection \<open>Primes on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

lemma Suc_0_not_prime_nat [simp]: "\<not> prime (Suc 0)"
  by sorry

lemma prime_ge_2_nat:
  "p \<ge> 2" if "prime p" for p :: nat
  by sorry

lemma prime_ge_2_int:
  "p \<ge> 2" if "prime p" for p :: int
  by sorry

lemma prime_ge_0_int: "prime p \<Longrightarrow> p \<ge> (0::int)"
  by sorry

lemma prime_gt_0_nat: "prime p \<Longrightarrow> p > (0::nat)"
  by sorry

(* As a simp or intro rule,

     prime p \<Longrightarrow> p > 0

   wreaks havoc here. When the premise includes \<forall>x \<in># M. prime x, it
   leads to the backchaining

     x > 0
     prime x
     x \<in># M   which is, unfortunately,
     count M x > 0  FIXME no, this is obsolete
*)

lemma prime_gt_0_int: "prime p \<Longrightarrow> p > (0::int)"
  by sorry

lemma prime_ge_1_nat: "prime p \<Longrightarrow> p \<ge> (1::nat)"
  by sorry

lemma prime_ge_Suc_0_nat: "prime p \<Longrightarrow> p \<ge> Suc 0"
  by sorry

lemma prime_ge_1_int: "prime p \<Longrightarrow> p \<ge> (1::int)"
  by sorry

lemma prime_gt_1_nat: "prime p \<Longrightarrow> p > (1::nat)"
  by sorry

lemma prime_gt_Suc_0_nat: "prime p \<Longrightarrow> p > Suc 0"
  by sorry

lemma prime_gt_1_int: "prime p \<Longrightarrow> p > (1::int)"
  by sorry

lemma prime_natI:
  "prime p" if "p \<ge> 2" and "\<And>m n. p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n" for p :: nat
  by sorry

lemma prime_intI:
  "prime p" if "p \<ge> 2" and "\<And>m n. p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n" for p :: int
  by sorry

lemma prime_elem_nat_iff [simp]:
  "prime_elem n \<longleftrightarrow> prime n" for n :: nat
  by sorry

lemma prime_elem_iff_prime_abs [simp]:
  "prime_elem k \<longleftrightarrow> prime \<bar>k\<bar>" for k :: int
  by sorry

lemma prime_nat_int_transfer [simp]:
  "prime (int n) \<longleftrightarrow> prime n" (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma prime_nat_iff_prime [simp]:
  "prime (nat k) \<longleftrightarrow> prime k"
  by sorry

lemma prime_int_nat_transfer:
  "prime k \<longleftrightarrow> k \<ge> 0 \<and> prime (nat k)"
  by sorry

lemma prime_nat_naiveI:
  "prime p" if "p \<ge> 2" and dvd: "\<And>n. n dvd p \<Longrightarrow> n = 1 \<or> n = p" for p :: nat
  by sorry

lemma prime_int_naiveI:
  "prime p" if "p \<ge> 2" and dvd: "\<And>k. k dvd p \<Longrightarrow> \<bar>k\<bar> = 1 \<or> \<bar>k\<bar> = p" for p :: int
  by sorry

lemma prime_nat_iff:
  "prime (n :: nat) \<longleftrightarrow> (1 < n \<and> (\<forall>m. m dvd n \<longrightarrow> m = 1 \<or> m = n))"
  by sorry

lemma prime_nat_iff':
  "prime (p :: nat) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {2..<p}. \<not> n dvd p)"
  by sorry

lemma prime_int_iff:
  "prime (n::int) \<longleftrightarrow> (1 < n \<and> (\<forall>m. m \<ge> 0 \<and> m dvd n \<longrightarrow> m = 1 \<or> m = n))"
  by sorry

lemma prime_int_iff':
  "prime (p :: int) \<longleftrightarrow> p > 1 \<and> (\<forall>n \<in> {2..<p}. \<not> n dvd p)" (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma prime_nat_not_dvd:
  assumes "prime p" "p > n" "n \<noteq> (1::nat)"
  shows   "\<not>n dvd p"
  by sorry

lemma prime_int_not_dvd:
  assumes "prime p" "p > n" "n > (1::int)"
  shows   "\<not>n dvd p"
  by sorry

lemma prime_odd_nat: "prime p \<Longrightarrow> p > (2::nat) \<Longrightarrow> odd p"
  by sorry

lemma prime_odd_int: "prime p \<Longrightarrow> p > (2::int) \<Longrightarrow> odd p"
  by sorry

lemma prime_int_altdef:
  "prime p = (1 < p \<and> (\<forall>m::int. m \<ge> 0 \<longrightarrow> m dvd p \<longrightarrow>
    m = 1 \<or> m = p))"
  by sorry

lemma not_prime_eq_prod_nat:
  assumes "m > 1" "\<not> prime (m::nat)"
  shows   "\<exists>n k. n = m * k \<and> 1 < m \<and> m < n \<and> 1 < k \<and> k < n"
  by sorry


subsection \<open>Make prime naively executable\<close>

lemma prime_int_numeral_eq [simp]:
  "prime (numeral m :: int) \<longleftrightarrow> prime (numeral m :: nat)"
  by sorry

class check_prime_by_range = normalization_semidom + discrete_linordered_semidom +
  assumes prime_iff: \<open>prime a \<longleftrightarrow> 1 < a \<and> (\<forall>d\<in>{2..a div 2}. \<not> d dvd a)\<close>
begin

lemma two_is_prime [simp]:
  \<open>prime 2\<close>
  by sorry

end

lemma divisor_less_eq_half_nat:
  \<open>m \<le> n div 2\<close> if \<open>m dvd n\<close> \<open>m < n\<close> for m n :: nat
  by sorry

instance nat :: check_prime_by_range
  apply standard
  apply (auto simp add: prime_nat_iff)
  apply (rule ccontr)
  apply (auto simp add: neq_iff)
  apply (metis One_nat_def Suc_1 Suc_leI atLeastAtMost_iff divisor_less_eq_half_nat)
  done

lemma two_is_prime_nat [simp]:
  \<open>prime (2::nat)\<close>
  by sorry

lemma divisor_less_eq_half_int:
  \<open>k \<le> l div 2\<close> if \<open>k dvd l\<close> \<open>k < l\<close> \<open>l \<ge> 0\<close> \<open>k \<ge> 0\<close> for k l :: int
  by sorry

instance int :: check_prime_by_range
  apply standard
  apply (auto simp add: prime_int_iff)
  apply (smt (verit) int_div_less_self)
  apply (rule ccontr)
  apply (auto simp add: neq_iff zdvd_not_zless)
  apply (metis div_by_0 dvd_div_eq_0_iff less_le_not_le one_dvd order_le_less
      zdvd_not_zless)
  apply (metis atLeastAtMost_iff divisor_less_eq_half_int dvd_div_eq_0_iff
      int_one_le_iff_zero_less nle_le one_add_one pos_imp_zdiv_nonneg_iff zdiv_eq_0_iff
      zless_imp_add1_zle)
  done

lemma prime_nat_numeral_eq [simp]: \<comment> \<open>TODO Sieve Of Erathosthenes might speed this up\<close>
  "prime (numeral m :: nat) \<longleftrightarrow>
    (1::nat) < numeral m \<and>
    (\<forall>n::nat \<in> set [2..<Suc (numeral m div 2)]. \<not> n dvd numeral m)"
  by sorry

context check_prime_by_range
begin

definition check_divisors :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>check_divisors l u a \<longleftrightarrow> (\<forall>d\<in>{l..u}. \<not> d dvd a)\<close>

lemma check_divisors_rec [code]:
  \<open>check_divisors l u a \<longleftrightarrow> u < l \<or> (\<not> l dvd a \<and> check_divisors (l + 1) u a)\<close>
  by sorry
  done

lemma prime_eq_check_divisors [code]:
  \<open>prime a \<longleftrightarrow> a > 1 \<and> check_divisors 2 (a div 2) a\<close>
  by sorry

end


subsection \<open>Largest exponent of a prime factor\<close>

lemma prime_factor_nat:
  "n \<noteq> (1::nat) \<Longrightarrow> \<exists>p. prime p \<and> p dvd n"
  by sorry

lemma prime_factor_int:
  fixes k :: int
  assumes "\<bar>k\<bar> \<noteq> 1"
  obtains p where "prime p" "p dvd k"
  by sorry

text\<open>Possibly duplicates other material, but avoid the complexities of multisets.\<close>
  
lemma prime_power_cancel_less:
  assumes "prime p" and eq: "m * (p ^ k) = m' * (p ^ k')" and less: "k < k'" and "\<not> p dvd m"
  shows False
  by sorry

lemma prime_power_cancel:
  assumes "prime p" and eq: "m * (p ^ k) = m' * (p ^ k')" and "\<not> p dvd m" "\<not> p dvd m'"
  shows "k = k'"
  by sorry

lemma prime_power_cancel2:
  assumes "prime p" "m * (p ^ k) = m' * (p ^ k')" "\<not> p dvd m" "\<not> p dvd m'"
  obtains "m = m'" "k = k'"
  by sorry

lemma prime_power_canonical:
  fixes m :: nat
  assumes "prime p" "m > 0"
  shows "\<exists>k n. \<not> p dvd n \<and> m = n * p ^ k"
  by sorry


subsection \<open>Infinitely many primes\<close>

lemma next_prime_bound: "\<exists>p::nat. prime p \<and> n < p \<and> p \<le> fact n + 1"
  by sorry

lemma bigger_prime: "\<exists>p. prime p \<and> p > (n::nat)"
  by sorry

lemma primes_infinite: "\<not> (finite {(p::nat). prime p})"
  by sorry

subsection \<open>Powers of Primes\<close>

text\<open>Versions for type nat only\<close>

lemma prime_product:
  fixes p::nat
  assumes "prime (p * q)"
  shows "p = 1 \<or> q = 1"
  by sorry

(* TODO: Generalise? *)
lemma prime_power_mult_nat:
  fixes p :: nat
  assumes p: "prime p" and xy: "x * y = p ^ k"
  shows "\<exists>i j. x = p ^ i \<and> y = p^ j"
  by sorry

lemma prime_power_exp_nat:
  fixes p::nat
  assumes p: "prime p" and n: "n \<noteq> 0"
    and xn: "x^n = p^k" shows "\<exists>i. x = p^i"
  by sorry

lemma divides_primepow_nat:
  fixes p :: nat
  assumes p: "prime p"
  shows "d dvd p ^ k \<longleftrightarrow> (\<exists>i\<le>k. d = p ^ i)"
  by sorry

lemma gcd_prime_int:
  assumes "prime (p :: int)"
  shows   "gcd p k = (if p dvd k then p else 1)"
  by sorry


subsection \<open>Chinese Remainder Theorem Variants\<close>

lemma bezout_gcd_nat:
  fixes a::nat shows "\<exists>x y. a * x - b * y = gcd a b \<or> b * x - a * y = gcd a b"
  by sorry
by (metis bezout_nat diff_add_inverse gcd_add_mult gcd.commute
  gcd_nat.right_neutral mult_0)

lemma gcd_bezout_sum_nat:
  fixes a::nat
  assumes "a * x + b * y = d"
  shows "gcd a b dvd d"
  by sorry


text \<open>A binary form of the Chinese Remainder Theorem.\<close>

(* TODO: Generalise? *)
lemma chinese_remainder:
  fixes a::nat  assumes ab: "coprime a b" and a: "a \<noteq> 0" and b: "b \<noteq> 0"
  shows "\<exists>x q1 q2. x = u + q1 * a \<and> x = v + q2 * b"
  by sorry

text \<open>Primality\<close>

lemma coprime_bezout_strong:
  fixes a::nat assumes "coprime a b"  "b \<noteq> 1"
  shows "\<exists>x y. a * x = b * y + 1"
  by sorry

lemma bezout_prime:
  assumes p: "prime p" and pa: "\<not> p dvd a"
  shows "\<exists>x y. a*x = Suc (p*y)"
  by sorry
(* END TODO *)



subsection \<open>Multiplicity and primality for natural numbers and integers\<close>

lemma prime_factors_gt_0_nat:
  "p \<in> prime_factors x \<Longrightarrow> p > (0::nat)"
  by sorry

lemma prime_factors_gt_0_int:
  "p \<in> prime_factors x \<Longrightarrow> p > (0::int)"
  by sorry

lemma prime_factors_ge_0_int [elim]: (* FIXME !? *)
  fixes n :: int
  shows "p \<in> prime_factors n \<Longrightarrow> p \<ge> 0"
  by sorry
  
lemma prod_mset_prime_factorization_int:
  fixes n :: int
  assumes "n > 0"
  shows   "prod_mset (prime_factorization n) = n"
  by sorry

lemma prime_factorization_exists_nat:
  "n > 0 \<Longrightarrow> (\<exists>M. (\<forall>p::nat \<in> set_mset M. prime p) \<and> n = (\<Prod>i \<in># M. i))"
  by sorry

lemma prod_mset_prime_factorization_nat [simp]: 
  "(n::nat) > 0 \<Longrightarrow> prod_mset (prime_factorization n) = n"
  by sorry

lemma prime_factorization_nat:
    "n > (0::nat) \<Longrightarrow> n = (\<Prod>p \<in> prime_factors n. p ^ multiplicity p n)"
  by sorry

lemma prime_factorization_int:
    "n > (0::int) \<Longrightarrow> n = (\<Prod>p \<in> prime_factors n. p ^ multiplicity p n)"
  by sorry

lemma prime_factorization_unique_nat:
  fixes f :: "nat \<Rightarrow> _"
  assumes S_eq: "S = {p. 0 < f p}"
    and "finite S"
    and S: "\<forall>p\<in>S. prime p" "n = (\<Prod>p\<in>S. p ^ f p)"
  shows "S = prime_factors n \<and> (\<forall>p. prime p \<longrightarrow> f p = multiplicity p n)"
  by sorry

lemma prime_factorization_unique_int:
  fixes f :: "int \<Rightarrow> _"
  assumes S_eq: "S = {p. 0 < f p}"
    and "finite S"
    and S: "\<forall>p\<in>S. prime p" "abs n = (\<Prod>p\<in>S. p ^ f p)"
  shows "S = prime_factors n \<and> (\<forall>p. prime p \<longrightarrow> f p = multiplicity p n)"
  by sorry

lemma prime_factors_characterization_nat:
  "S = {p. 0 < f (p::nat)} \<Longrightarrow>
    finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow> n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> prime_factors n = S"
  by sorry

lemma prime_factors_characterization'_nat:
  "finite {p. 0 < f (p::nat)} \<Longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow>
      prime_factors (\<Prod>p | 0 < f p. p ^ f p) = {p. 0 < f p}"
  by sorry

lemma prime_factors_characterization_int:
  "S = {p. 0 < f (p::int)} \<Longrightarrow> finite S \<Longrightarrow>
    \<forall>p\<in>S. prime p \<Longrightarrow> abs n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> prime_factors n = S"
  by sorry

(* TODO Move *)
lemma abs_prod: "abs (prod f A :: 'a :: linordered_idom) = prod (\<lambda>x. abs (f x)) A"
  by sorry

lemma primes_characterization'_int [rule_format]:
  "finite {p. p \<ge> 0 \<and> 0 < f (p::int)} \<Longrightarrow> \<forall>p. 0 < f p \<longrightarrow> prime p \<Longrightarrow>
      prime_factors (\<Prod>p | p \<ge> 0 \<and> 0 < f p. p ^ f p) = {p. p \<ge> 0 \<and> 0 < f p}"
  by sorry

lemma multiplicity_characterization_nat:
  "S = {p. 0 < f (p::nat)} \<Longrightarrow> finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow> prime p \<Longrightarrow>
    n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> multiplicity p n = f p"
  by sorry

lemma multiplicity_characterization'_nat: "finite {p. 0 < f (p::nat)} \<longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<longrightarrow> prime p \<longrightarrow>
      multiplicity p (\<Prod>p | 0 < f p. p ^ f p) = f p"
  by sorry

lemma multiplicity_characterization_int: "S = {p. 0 < f (p::int)} \<Longrightarrow>
    finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow> prime p \<Longrightarrow> n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> multiplicity p n = f p"
  by sorry

lemma multiplicity_characterization'_int [rule_format]:
  "finite {p. p \<ge> 0 \<and> 0 < f (p::int)} \<Longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow> prime p \<Longrightarrow>
      multiplicity p (\<Prod>p | p \<ge> 0 \<and> 0 < f p. p ^ f p) = f p"
  by sorry

lemma multiplicity_one_nat [simp]: "multiplicity p (Suc 0) = 0"
  by sorry

lemma multiplicity_eq_nat:
  fixes x and y::nat
  assumes "x > 0" "y > 0" "\<And>p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows "x = y"
  by sorry

lemma multiplicity_eq_int:
  fixes x y :: int
  assumes "x > 0" "y > 0" "\<And>p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows "x = y"
  by sorry

lemma multiplicity_prod_prime_powers:
  assumes "finite S" "\<And>x. x \<in> S \<Longrightarrow> prime x" "prime p"
  shows   "multiplicity p (\<Prod>p \<in> S. p ^ f p) = (if p \<in> S then f p else 0)"
  by sorry

lemma prime_factorization_prod_mset:
  assumes "0 \<notin># A"
  shows "prime_factorization (prod_mset A) = \<Sum>\<^sub>#(image_mset prime_factorization A)"
  by sorry

lemma prime_factors_prod:
  assumes "finite A" and "0 \<notin> f ` A"
  shows "prime_factors (prod f A) = \<Union>((prime_factors \<circ> f) ` A)"
  by sorry

lemma prime_factors_fact:
  "prime_factors (fact n) = {p \<in> {2..n}. prime p}" (is "?M = ?N")
  by sorry

lemma prime_dvd_fact_iff:
  assumes "prime p"
  shows "p dvd fact n \<longleftrightarrow> p \<le> n"
  by sorry

lemma dvd_choose_prime:
  assumes kn: "k < n" and k: "k \<noteq> 0" and n: "n \<noteq> 0" and prime_n: "prime n"
  shows "n dvd (n choose k)"
  by sorry

lemma (in ring_1) minus_power_prime_CHAR:
  assumes "p = CHAR('a)" "prime p"
  shows "(-x :: 'a) ^ p = -(x ^ p)"
  by sorry


subsection \<open>Rings and fields with prime characteristic\<close>

text \<open>
  We introduce some type classes for rings and fields with prime characteristic.
\<close>

class semiring_prime_char = semiring_1 +
  assumes prime_char_aux: "\<exists>n. prime n \<and> of_nat n = (0 :: 'a)"
begin

lemma CHAR_pos [intro, simp]: "CHAR('a) > 0"
  by sorry

lemma CHAR_nonzero [simp]: "CHAR('a) \<noteq> 0"
  by sorry

lemma CHAR_prime [intro, simp]: "prime CHAR('a)"
  by sorry

end

lemma semiring_prime_charI [intro?]:
  "prime CHAR('a :: semiring_1) \<Longrightarrow> OFCLASS('a, semiring_prime_char_class)"
  by sorry

lemma idom_prime_charI [intro?]:
  assumes "CHAR('a :: idom) > 0"
  shows   "OFCLASS('a, semiring_prime_char_class)"
  by sorry

class comm_semiring_prime_char = comm_semiring_1 + semiring_prime_char
class comm_ring_prime_char = comm_ring_1 + semiring_prime_char
begin
subclass comm_semiring_prime_char ..
end
class idom_prime_char = idom + semiring_prime_char
begin
subclass comm_ring_prime_char ..
end

class field_prime_char = field +
  assumes pos_char_exists: "\<exists>n>0. of_nat n = (0 :: 'a)"
begin
subclass idom_prime_char
  apply standard
  using pos_char_exists local.CHAR_pos_iff local.of_nat_CHAR local.prime_CHAR_semidom by blast
end

lemma field_prime_charI [intro?]:
  "n > 0 \<Longrightarrow> of_nat n = (0 :: 'a :: field) \<Longrightarrow> OFCLASS('a, field_prime_char_class)"
  by sorry

lemma field_prime_charI' [intro?]:
  "CHAR('a :: field) > 0 \<Longrightarrow> OFCLASS('a, field_prime_char_class)"
  by sorry


subsection \<open>Finite fields\<close>

class finite_field = field_prime_char + finite

lemma finite_fieldI [intro?]:
  assumes "finite (UNIV :: 'a :: field set)"
  shows   "OFCLASS('a, finite_field_class)"
  by sorry

text \<open>
  On a finite field with \<open>n\<close> elements, taking the \<open>n\<close>-th power of an element
  is the identity. This is an obvious consequence of the fact that the multiplicative group of
  the field is a finite group of order \<open>n - 1\<close>, so \<open>x^n = 1\<close> for any non-zero \<open>x\<close>.

  Note that this result is sharp in the sense that the multiplicative group of a
  finite field is cyclic, i.e.\ it contains an element of order \<open>n - 1\<close>.
  (We don't prove this here.)
\<close>
lemma finite_field_power_card_eq_same:
  fixes x :: "'a :: finite_field"
  shows   "x ^ card (UNIV :: 'a set) = x"
  by sorry

lemma finite_field_power_card_power_eq_same:
  fixes x :: "'a :: finite_field"
  assumes "m = card (UNIV :: 'a set) ^ n"
  shows   "x ^ m = x"
  by sorry

class enum_finite_field = finite_field +
  fixes enum_finite_field :: "nat \<Rightarrow> 'a"
  assumes enum_finite_field: "enum_finite_field ` {..<card (UNIV :: 'a set)} = UNIV"
begin

lemma inj_on_enum_finite_field: "inj_on enum_finite_field {..<card (UNIV :: 'a set)}"
  by sorry

end

text \<open>
  To get rid of the pending sort hypotheses, we prove that the field with 2 elements is indeed
  a finite field.
\<close>
typedef gf2 = "{0, 1 :: nat}"
  by auto

setup_lifting type_definition_gf2

instantiation gf2 :: field
begin
lift_definition zero_gf2 :: "gf2" is "0" by auto
lift_definition one_gf2 :: "gf2" is "1" by auto
lift_definition uminus_gf2 :: "gf2 \<Rightarrow> gf2" is "\<lambda>x. x" .
lift_definition plus_gf2 :: "gf2 \<Rightarrow> gf2 \<Rightarrow> gf2" is "\<lambda>x y. if x = y then 0 else 1" by auto
lift_definition minus_gf2 :: "gf2 \<Rightarrow> gf2 \<Rightarrow> gf2" is "\<lambda>x y. if x = y then 0 else 1" by auto
lift_definition times_gf2 :: "gf2 \<Rightarrow> gf2 \<Rightarrow> gf2" is "\<lambda>x y. x * y" by auto
lift_definition inverse_gf2 :: "gf2 \<Rightarrow> gf2" is "\<lambda>x. x" .
lift_definition divide_gf2 :: "gf2 \<Rightarrow> gf2 \<Rightarrow> gf2" is "\<lambda>x y. x * y" by auto

instance
  by standard (transfer; fastforce)+

end

instance gf2 :: finite_field
proof
  interpret type_definition Rep_gf2 Abs_gf2 "{0, 1 :: nat}"
    by (rule type_definition_gf2)
  show "finite (UNIV :: gf2 set)"
    by (metis Abs_image finite.emptyI finite.insertI finite_imageI)
qed


subsection \<open>The Freshman's Dream in rings of prime characteristic\<close>

lemma (in comm_semiring_1) freshmans_dream:
  fixes x y :: 'a and n :: nat
  assumes "prime CHAR('a)"
  assumes n_def: "n = CHAR('a)"
  shows   "(x + y) ^ n = x ^ n + y ^ n"
  by sorry

lemma (in comm_semiring_1) freshmans_dream':
  assumes [simp]: "prime CHAR('a)" and "m = CHAR('a) ^ n"
  shows "(x + y :: 'a) ^ m = x ^ m + y ^ m"
  by sorry

lemma (in comm_semiring_1) freshmans_dream_sum:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "prime CHAR('a)" and "n = CHAR('a)"
  shows "sum f A ^ n = sum (\<lambda>i. f i ^ n) A"
  by sorry

lemma (in comm_semiring_1) freshmans_dream_sum':
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "prime CHAR('a)" "m = CHAR('a) ^ n"
  shows   "sum f A ^ m = sum (\<lambda>i. f i ^ m) A"
  by sorry



(* TODO Legacy names *)
lemmas prime_imp_coprime_nat = prime_imp_coprime[where ?'a = nat]
lemmas prime_imp_coprime_int = prime_imp_coprime[where ?'a = int]
lemmas prime_dvd_mult_nat = prime_dvd_mult_iff[where ?'a = nat]
lemmas prime_dvd_mult_int = prime_dvd_mult_iff[where ?'a = int]
lemmas prime_dvd_mult_eq_nat = prime_dvd_mult_iff[where ?'a = nat]
lemmas prime_dvd_mult_eq_int = prime_dvd_mult_iff[where ?'a = int]
lemmas prime_dvd_power_nat = prime_dvd_power[where ?'a = nat]
lemmas prime_dvd_power_int = prime_dvd_power[where ?'a = int]
lemmas prime_dvd_power_nat_iff = prime_dvd_power_iff[where ?'a = nat]
lemmas prime_dvd_power_int_iff = prime_dvd_power_iff[where ?'a = int]
lemmas prime_imp_power_coprime_nat = prime_imp_power_coprime[where ?'a = nat]
lemmas prime_imp_power_coprime_int = prime_imp_power_coprime[where ?'a = int]
lemmas primes_coprime_nat = primes_coprime[where ?'a = nat]
lemmas primes_coprime_int = primes_coprime[where ?'a = nat]
lemmas prime_divprod_pow_nat = prime_elem_divprod_pow[where ?'a = nat]
lemmas prime_exp = prime_elem_power_iff[where ?'a = nat]

end
