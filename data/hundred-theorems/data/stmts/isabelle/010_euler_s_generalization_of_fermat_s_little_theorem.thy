(*  Title:      HOL/Number_Theory/Residues.thy
    Author:     Jeremy Avigad

An algebraic treatment of residue rings, and resulting proofs of
Euler's theorem and Wilson's theorem.
*)

section \<open>Residue rings\<close>

theory Residues
imports
  Cong
  "HOL-Algebra.Multiplicative_Group"
  Totient
begin

lemma (in ring_1) CHAR_dvd_CARD: "CHAR('a) dvd card (UNIV :: 'a set)"
  by sorry

definition QuadRes :: "int \<Rightarrow> int \<Rightarrow> bool"
  where "QuadRes p a = (\<exists>y. ([y^2 = a] (mod p)))"

definition Legendre :: "int \<Rightarrow> int \<Rightarrow> int"
  where "Legendre a p =
    (if ([a = 0] (mod p)) then 0
     else if QuadRes p a then 1
     else -1)"


subsection \<open>A locale for residue rings\<close>

definition residue_ring :: "int \<Rightarrow> int ring"
  where
    "residue_ring m =
      \<lparr>carrier = {0..m - 1},
       monoid.mult = \<lambda>x y. (x * y) mod m,
       one = 1,
       zero = 0,
       add = \<lambda>x y. (x + y) mod m\<rparr>"

locale residues =
  fixes m :: int and R (structure)
  assumes m_gt_one: "m > 1"
  defines R_m_def: "R \<equiv> residue_ring m"
begin

lemma abelian_group: "abelian_group R"
  by sorry

lemma comm_monoid: "comm_monoid R"
  by sorry

interpretation comm_monoid R
  using comm_monoid by blast

lemma cring: "cring R"
  by sorry

end

sublocale residues < cring
  by (rule cring)


context residues
begin

text \<open>
  These lemmas translate back and forth between internal and
  external concepts.
\<close>

lemma res_carrier_eq: "carrier R = {0..m - 1}"
  by sorry

lemma res_add_eq: "x \<oplus> y = (x + y) mod m"
  by sorry

lemma res_mult_eq: "x \<otimes> y = (x * y) mod m"
  by sorry

lemma res_zero_eq: "\<zero> = 0"
  by sorry

lemma res_one_eq: "\<one> = 1"
  by sorry

lemma res_units_eq: "Units R = {x. 0 < x \<and> x < m \<and> coprime x m}" (is "_ = ?rhs")
  by sorry

lemma res_neg_eq: "\<ominus> x = (- x) mod m"
  by sorry

lemma finite [iff]: "finite (carrier R)"
  by sorry

lemma finite_Units [iff]: "finite (Units R)"
  by sorry

text \<open>
  The function \<open>a \<mapsto> a mod m\<close> maps the integers to the
  residue classes. The following lemmas show that this mapping
  respects addition and multiplication on the integers.
\<close>

lemma mod_in_carrier [iff]: "a mod m \<in> carrier R"
  by sorry

lemma add_cong: "(x mod m) \<oplus> (y mod m) = (x + y) mod m"
  by sorry

lemma mult_cong: "(x mod m) \<otimes> (y mod m) = (x * y) mod m"
  by sorry

lemma zero_cong: "\<zero> = 0"
  by sorry

lemma one_cong: "\<one> = 1 mod m"
  by sorry

(* FIXME revise algebra library to use 1? *)
lemma pow_cong: "(x mod m) [^] n = x^n mod m"
  by sorry

lemma neg_cong: "\<ominus> (x mod m) = (- x) mod m"
  by sorry

lemma (in residues) prod_cong: "finite A \<Longrightarrow> (\<Otimes>i\<in>A. (f i) mod m) = (\<Prod>i\<in>A. f i) mod m"
  by sorry

lemma (in residues) sum_cong: "finite A \<Longrightarrow> (\<Oplus>i\<in>A. (f i) mod m) = (\<Sum>i\<in>A. f i) mod m"
  by sorry

lemma mod_in_res_units [simp]:
  assumes "1 < m" and "coprime a m"
  shows "a mod m \<in> Units R"
  by sorry

lemma res_eq_to_cong: "(a mod m) = (b mod m) \<longleftrightarrow> [a = b] (mod m)"
  by sorry


text \<open>Simplifying with these will translate a ring equation in R to a congruence.\<close>
lemmas res_to_cong_simps =
  add_cong mult_cong pow_cong one_cong
  prod_cong sum_cong neg_cong res_eq_to_cong

text \<open>Other useful facts about the residue ring.\<close>
lemma one_eq_neg_one: "\<one> = \<ominus> \<one> \<Longrightarrow> m = 2"
  by sorry

end


subsection \<open>Prime residues\<close>

locale residues_prime =
  fixes p :: nat and R (structure)
  assumes p_prime [intro]: "prime p"
  defines "R \<equiv> residue_ring (int p)"

sublocale residues_prime < residues p
proof
  show "1 < int p"
    using prime_gt_1_nat by auto
qed

context residues_prime
begin

lemma p_coprime_left:
  "coprime p a \<longleftrightarrow> \<not> p dvd a"
  by sorry

lemma p_coprime_right:
  "coprime a p  \<longleftrightarrow> \<not> p dvd a"
  by sorry

lemma p_coprime_left_int:
  "coprime (int p) a \<longleftrightarrow> \<not> int p dvd a"
  by sorry

lemma p_coprime_right_int:
  "coprime a (int p) \<longleftrightarrow> \<not> int p dvd a"
  by sorry

lemma is_field: "field R"
  by sorry

lemma res_prime_units_eq: "Units R = {1..p - 1}"
  by sorry

end

sublocale residues_prime < field
  by (rule is_field)


section \<open>Test cases: Euler's theorem and Wilson's theorem\<close>

subsection \<open>Euler's theorem\<close>

lemma (in residues) totatives_eq:
  "totatives (nat m) = nat ` Units R"
  by sorry

lemma (in residues) totient_eq:
  "totient (nat m) = card (Units R)"
  by sorry

lemma (in residues_prime) prime_totient_eq: "totient p = p - 1"
  by sorry

lemma (in residues) euler_theorem:
  assumes "coprime a m"
  shows "[a ^ totient (nat m) = 1] (mod m)"
  by sorry

lemma euler_theorem:
  fixes a m :: nat
  assumes "coprime a m"
  shows "[a ^ totient m = 1] (mod m)"
  by sorry

lemma fermat_theorem:
  fixes p a :: nat
  assumes "prime p" and "\<not> p dvd a"
  shows "[a ^ (p - 1) = 1] (mod p)"
  by sorry


subsection \<open>Wilson's theorem\<close>

lemma (in field) inv_pair_lemma: "x \<in> Units R \<Longrightarrow> y \<in> Units R \<Longrightarrow>
    {x, inv x} \<noteq> {y, inv y} \<Longrightarrow> {x, inv x} \<inter> {y, inv y} = {}"
  by sorry


lemma (in residues_prime) wilson_theorem1:
  assumes a: "p > 2"
  shows "[fact (p - 1) = (-1::int)] (mod p)"
  by sorry

lemma wilson_theorem:
  assumes "prime p"
  shows "[fact (p - 1) = - 1] (mod p)"
  by sorry

text \<open>
  This result can be transferred to the multiplicative group of
  \<open>\<int>/p\<int>\<close> for \<open>p\<close> prime.\<close>

lemma mod_nat_int_pow_eq:
  fixes n :: nat and p a :: int
  shows "a \<ge> 0 \<Longrightarrow> p \<ge> 0 \<Longrightarrow> (nat a ^ n) mod (nat p) = nat ((a ^ n) mod p)"
  by sorry

theorem residue_prime_mult_group_has_gen:
 fixes p :: nat
 assumes prime_p : "prime p"
 shows "\<exists>a \<in> {1 .. p - 1}. {1 .. p - 1} = {a^i mod p|i . i \<in> UNIV}"
  by sorry


subsection \<open>Upper bound for the number of $n$-th roots\<close>

lemma roots_mod_prime_bound:
  fixes n c p :: nat
  assumes "prime p" "n > 0"
  defines "A \<equiv> {x\<in>{..<p}. [x ^ n = c] (mod p)}"
  shows   "card A \<le> n"
  by sorry


end
