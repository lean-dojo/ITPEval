(*  Title:      HOL/GCD.thy
    Author:     Christophe Tabacznyj
    Author:     Lawrence C. Paulson
    Author:     Amine Chaieb
    Author:     Thomas M. Rasmussen
    Author:     Jeremy Avigad
    Author:     Tobias Nipkow

This file deals with the functions gcd and lcm.  Definitions and
lemmas are proved uniformly for the natural numbers and integers.

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
*)

section \<open>Greatest common divisor and least common multiple\<close>

theory GCD
  imports Groups_List Code_Numeral
begin

subsection \<open>Abstract bounded quasi semilattices as common foundation\<close>

locale bounded_quasi_semilattice = abel_semigroup +
  fixes top :: 'a  (\<open>\<^bold>\<top>\<close>) and bot :: 'a  (\<open>\<^bold>\<bottom>\<close>)
    and normalize :: "'a \<Rightarrow> 'a"
  assumes idem_normalize [simp]: "a \<^bold>* a = normalize a"
    and normalize_left_idem [simp]: "normalize a \<^bold>* b = a \<^bold>* b"
    and normalize_idem [simp]: "normalize (a \<^bold>* b) = a \<^bold>* b"
    and normalize_top [simp]: "normalize \<^bold>\<top> = \<^bold>\<top>"
    and normalize_bottom [simp]: "normalize \<^bold>\<bottom> = \<^bold>\<bottom>"
    and top_left_normalize [simp]: "\<^bold>\<top> \<^bold>* a = normalize a"
    and bottom_left_bottom [simp]: "\<^bold>\<bottom> \<^bold>* a = \<^bold>\<bottom>"
begin

lemma left_idem [simp]:
  "a \<^bold>* (a \<^bold>* b) = a \<^bold>* b"
  by sorry

lemma right_idem [simp]:
  "(a \<^bold>* b) \<^bold>* b = a \<^bold>* b"
  by sorry

lemma comp_fun_idem: "comp_fun_idem f"
  by sorry

interpretation comp_fun_idem f
  by (fact comp_fun_idem)

lemma top_right_normalize [simp]:
  "a \<^bold>* \<^bold>\<top> = normalize a"
  by sorry

lemma bottom_right_bottom [simp]:
  "a \<^bold>* \<^bold>\<bottom> = \<^bold>\<bottom>"
  by sorry

lemma normalize_right_idem [simp]:
  "a \<^bold>* normalize b = a \<^bold>* b"
  by sorry

end

locale bounded_quasi_semilattice_set = bounded_quasi_semilattice
begin

interpretation comp_fun_idem f
  by (fact comp_fun_idem)

definition F :: "'a set \<Rightarrow> 'a"
where
  eq_fold: "F A = (if finite A then Finite_Set.fold f \<^bold>\<top> A else \<^bold>\<bottom>)"

lemma infinite [simp]:
  "infinite A \<Longrightarrow> F A = \<^bold>\<bottom>"
  by sorry

lemma set_eq_fold [code]:
  "F (set xs) = fold f xs \<^bold>\<top>"
  by sorry

lemma empty [simp]:
  "F {} = \<^bold>\<top>"
  by sorry

lemma insert [simp]:
  "F (insert a A) = a \<^bold>* F A"
  by sorry

lemma normalize [simp]:
  "normalize (F A) = F A"
  by sorry

lemma in_idem:
  assumes "a \<in> A"
  shows "a \<^bold>* F A = F A"
  by sorry

lemma union:
  "F (A \<union> B) = F A \<^bold>* F B"
  by sorry

lemma remove:
  assumes "a \<in> A"
  shows "F A = a \<^bold>* F (A - {a})"
  by sorry

lemma insert_remove:
  "F (insert a A) = a \<^bold>* F (A - {a})"
  by sorry

lemma subset:
  assumes "B \<subseteq> A"
  shows "F B \<^bold>* F A = F A"
  by sorry

end

subsection \<open>Abstract GCD and LCM\<close>

class gcd = zero + one + dvd +
  fixes gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and lcm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

class Gcd = gcd +
  fixes Gcd :: "'a set \<Rightarrow> 'a"
    and Lcm :: "'a set \<Rightarrow> 'a"

syntax
  "_GCD1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           (\<open>(\<open>indent=3 notation=\<open>binder GCD\<close>\<close>GCD _./ _)\<close> [0, 10] 10)
  "_GCD"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  (\<open>(\<open>indent=3 notation=\<open>binder GCD\<close>\<close>GCD _\<in>_./ _)\<close> [0, 0, 10] 10)
  "_LCM1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           (\<open>(\<open>indent=3 notation=\<open>binder LCM\<close>\<close>LCM _./ _)\<close> [0, 10] 10)
  "_LCM"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  (\<open>(\<open>indent=3 notation=\<open>binder LCM\<close>\<close>LCM _\<in>_./ _)\<close> [0, 0, 10] 10)

syntax_consts
  "_GCD1" "_GCD" \<rightleftharpoons> Gcd and
  "_LCM1" "_LCM" \<rightleftharpoons> Lcm

translations
  "GCD x y. f"   \<rightleftharpoons> "GCD x. GCD y. f"
  "GCD x. f"     \<rightleftharpoons> "CONST Gcd (CONST range (\<lambda>x. f))"
  "GCD x\<in>A. f"   \<rightleftharpoons> "CONST Gcd ((\<lambda>x. f) ` A)"
  "LCM x y. f"   \<rightleftharpoons> "LCM x. LCM y. f"
  "LCM x. f"     \<rightleftharpoons> "CONST Lcm (CONST range (\<lambda>x. f))"
  "LCM x\<in>A. f"   \<rightleftharpoons> "CONST Lcm ((\<lambda>x. f) ` A)"

class semiring_gcd = normalization_semidom + gcd +
  assumes gcd_dvd1 [iff]: "gcd a b dvd a"
    and gcd_dvd2 [iff]: "gcd a b dvd b"
    and gcd_greatest: "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd gcd a b"
    and normalize_gcd [simp]: "normalize (gcd a b) = gcd a b"
    and lcm_gcd: "lcm a b = normalize (a * b div gcd a b)"
begin

lemma gcd_greatest_iff [simp]: "a dvd gcd b c \<longleftrightarrow> a dvd b \<and> a dvd c"
  by sorry

lemma gcd_dvdI1: "a dvd c \<Longrightarrow> gcd a b dvd c"
  by sorry

lemma gcd_dvdI2: "b dvd c \<Longrightarrow> gcd a b dvd c"
  by sorry

lemma dvd_gcdD1: "a dvd gcd b c \<Longrightarrow> a dvd b"
  by sorry

lemma dvd_gcdD2: "a dvd gcd b c \<Longrightarrow> a dvd c"
  by sorry

lemma gcd_0_left [simp]: "gcd 0 a = normalize a"
  by sorry

lemma gcd_0_right [simp]: "gcd a 0 = normalize a"
  by sorry

lemma gcd_eq_0_iff [simp]: "gcd a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma unit_factor_gcd: "unit_factor (gcd a b) = (if a = 0 \<and> b = 0 then 0 else 1)"
  by sorry

lemma is_unit_gcd_iff [simp]:
  "is_unit (gcd a b) \<longleftrightarrow> gcd a b = 1"
  by sorry

sublocale gcd: abel_semigroup gcd
proof
  fix a b c
  show "gcd a b = gcd b a"
    by (rule associated_eqI) simp_all
  from gcd_dvd1 have "gcd (gcd a b) c dvd a"
    by (rule dvd_trans) simp
  moreover from gcd_dvd1 have "gcd (gcd a b) c dvd b"
    by (rule dvd_trans) simp
  ultimately have P1: "gcd (gcd a b) c dvd gcd a (gcd b c)"
    by (auto intro!: gcd_greatest)
  from gcd_dvd2 have "gcd a (gcd b c) dvd b"
    by (rule dvd_trans) simp
  moreover from gcd_dvd2 have "gcd a (gcd b c) dvd c"
    by (rule dvd_trans) simp
  ultimately have P2: "gcd a (gcd b c) dvd gcd (gcd a b) c"
    by (auto intro!: gcd_greatest)
  from P1 P2 show "gcd (gcd a b) c = gcd a (gcd b c)"
    by (rule associated_eqI) simp_all
qed

sublocale gcd: bounded_quasi_semilattice gcd 0 1 normalize
proof
  show "gcd a a = normalize a" for a
  proof -
    have "a dvd gcd a a"
      by (rule gcd_greatest) simp_all
    then show ?thesis
      by (auto intro: associated_eqI)
  qed
  show "gcd (normalize a) b = gcd a b" for a b
    using gcd_dvd1 [of "normalize a" b]
    by (auto intro: associated_eqI)
  show "gcd 1 a = 1" for a
    by (rule associated_eqI) simp_all
qed simp_all

lemma gcd_self: "gcd a a = normalize a"
  by sorry

lemma gcd_left_idem: "gcd a (gcd a b) = gcd a b"
  by sorry

lemma gcd_right_idem: "gcd (gcd a b) b = gcd a b"
  by sorry

lemma gcdI:
  assumes "c dvd a" and "c dvd b"
    and greatest: "\<And>d. d dvd a \<Longrightarrow> d dvd b \<Longrightarrow> d dvd c"
    and "normalize c = c"
  shows "c = gcd a b"
  by sorry

lemma gcd_unique:
  "d dvd a \<and> d dvd b \<and> normalize d = d \<and> (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  by sorry

lemma gcd_dvd_prod: "gcd a b dvd k * b"
  by sorry

lemma gcd_proj2_if_dvd: "b dvd a \<Longrightarrow> gcd a b = normalize b"
  by sorry

lemma gcd_proj1_if_dvd: "a dvd b \<Longrightarrow> gcd a b = normalize a"
  by sorry

lemma gcd_proj1_iff: "gcd m n = normalize m \<longleftrightarrow> m dvd n"
  by sorry

lemma gcd_proj2_iff: "gcd m n = normalize n \<longleftrightarrow> n dvd m"
  by sorry

lemma gcd_mult_left: "gcd (c * a) (c * b) = normalize (c * gcd a b)"
  by sorry

lemma gcd_mult_right: "gcd (a * c) (b * c) = normalize (gcd b a * c)"
  by sorry

lemma dvd_lcm1 [iff]: "a dvd lcm a b"
  by sorry

lemma dvd_lcm2 [iff]: "b dvd lcm a b"
  by sorry

lemma dvd_lcmI1: "a dvd b \<Longrightarrow> a dvd lcm b c"
  by sorry

lemma dvd_lcmI2: "a dvd c \<Longrightarrow> a dvd lcm b c"
  by sorry

lemma lcm_dvdD1: "lcm a b dvd c \<Longrightarrow> a dvd c"
  by sorry

lemma lcm_dvdD2: "lcm a b dvd c \<Longrightarrow> b dvd c"
  by sorry

lemma lcm_least:
  assumes "a dvd c" and "b dvd c"
  shows "lcm a b dvd c"
  by sorry

lemma lcm_least_iff [simp]: "lcm a b dvd c \<longleftrightarrow> a dvd c \<and> b dvd c"
  by sorry

lemma normalize_lcm [simp]: "normalize (lcm a b) = lcm a b"
  by sorry

lemma lcm_0_left [simp]: "lcm 0 a = 0"
  by sorry

lemma lcm_0_right [simp]: "lcm a 0 = 0"
  by sorry

lemma lcm_eq_0_iff: "lcm a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma zero_eq_lcm_iff: "0 = lcm a b \<longleftrightarrow> a = 0 \<or> b = 0"
  by sorry

lemma lcm_eq_1_iff [simp]: "lcm a b = 1 \<longleftrightarrow> is_unit a \<and> is_unit b"
  by sorry

lemma unit_factor_lcm: "unit_factor (lcm a b) = (if a = 0 \<or> b = 0 then 0 else 1)"
  by sorry

sublocale lcm: abel_semigroup lcm
proof
  fix a b c
  show "lcm a b = lcm b a"
    by (simp add: lcm_gcd ac_simps normalize_mult dvd_normalize_div)
  have "lcm (lcm a b) c dvd lcm a (lcm b c)"
    and "lcm a (lcm b c) dvd lcm (lcm a b) c"
    by (auto intro: lcm_least
      dvd_trans [of b "lcm b c" "lcm a (lcm b c)"]
      dvd_trans [of c "lcm b c" "lcm a (lcm b c)"]
      dvd_trans [of a "lcm a b" "lcm (lcm a b) c"]
      dvd_trans [of b "lcm a b" "lcm (lcm a b) c"])
  then show "lcm (lcm a b) c = lcm a (lcm b c)"
    by (rule associated_eqI) simp_all
qed

sublocale lcm: bounded_quasi_semilattice lcm 1 0 normalize
proof
  show "lcm a a = normalize a" for a
  proof -
    have "lcm a a dvd a"
      by (rule lcm_least) simp_all
    then show ?thesis
      by (auto intro: associated_eqI)
  qed
  show "lcm (normalize a) b = lcm a b" for a b
    using dvd_lcm1 [of "normalize a" b] unfolding normalize_dvd_iff
    by (auto intro: associated_eqI)
  show "lcm 1 a = normalize a" for a
    by (rule associated_eqI) simp_all
qed simp_all

lemma lcm_self: "lcm a a = normalize a"
  by sorry

lemma lcm_left_idem: "lcm a (lcm a b) = lcm a b"
  by sorry

lemma lcm_right_idem: "lcm (lcm a b) b = lcm a b"
  by sorry

lemma gcd_lcm:
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "gcd a b = normalize (a * b div lcm a b)"
  by sorry

lemma lcm_1_left: "lcm 1 a = normalize a"
  by sorry

lemma lcm_1_right: "lcm a 1 = normalize a"
  by sorry

lemma lcm_mult_left: "lcm (c * a) (c * b) = normalize (c * lcm a b)"
  by sorry

lemma lcm_mult_right: "lcm (a * c) (b * c) = normalize (lcm b a * c)"
  by sorry

lemma lcm_mult_unit1: "is_unit a \<Longrightarrow> lcm (b * a) c = lcm b c"
  by sorry

lemma lcm_mult_unit2: "is_unit a \<Longrightarrow> lcm b (c * a) = lcm b c"
  by sorry

lemma lcm_div_unit1:
  "is_unit a \<Longrightarrow> lcm (b div a) c = lcm b c"
  by sorry

lemma lcm_div_unit2: "is_unit a \<Longrightarrow> lcm b (c div a) = lcm b c"
  by sorry

lemma normalize_lcm_left: "lcm (normalize a) b = lcm a b"
  by sorry

lemma normalize_lcm_right: "lcm a (normalize b) = lcm a b"
  by sorry

lemma comp_fun_idem_gcd: "comp_fun_idem gcd"
  by sorry

lemma comp_fun_idem_lcm: "comp_fun_idem lcm"
  by sorry

lemma gcd_dvd_antisym: "gcd a b dvd gcd c d \<Longrightarrow> gcd c d dvd gcd a b \<Longrightarrow> gcd a b = gcd c d"
  by sorry

declare unit_factor_lcm [simp]

lemma lcmI:
  assumes "a dvd c" and "b dvd c" and "\<And>d. a dvd d \<Longrightarrow> b dvd d \<Longrightarrow> c dvd d"
    and "normalize c = c"
  shows "c = lcm a b"
  by sorry

lemma gcd_dvd_lcm [simp]: "gcd a b dvd lcm a b"
  by sorry

lemmas lcm_0 = lcm_0_right

lemma lcm_unique:
  "a dvd d \<and> b dvd d \<and> normalize d = d \<and> (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by sorry

lemma lcm_proj1_if_dvd:
  assumes "b dvd a" shows "lcm a b = normalize a"
  by sorry

lemma lcm_proj2_if_dvd: "a dvd b \<Longrightarrow> lcm a b = normalize b"
  by sorry

lemma lcm_proj1_iff: "lcm m n = normalize m \<longleftrightarrow> n dvd m"
  by sorry

lemma lcm_proj2_iff: "lcm m n = normalize n \<longleftrightarrow> m dvd n"
  by sorry

lemma gcd_mono: "a dvd c \<Longrightarrow> b dvd d \<Longrightarrow> gcd a b dvd gcd c d"
  by sorry

lemma lcm_mono: "a dvd c \<Longrightarrow> b dvd d \<Longrightarrow> lcm a b dvd lcm c d"
  by sorry

lemma dvd_productE:
  assumes "p dvd a * b"
  obtains x y where "p = x * y" "x dvd a" "y dvd b"
  by sorry

lemma gcd_mult_unit1: 
  assumes "is_unit a" shows "gcd (b * a) c = gcd b c"
  by sorry

lemma gcd_mult_unit2: "is_unit a \<Longrightarrow> gcd b (c * a) = gcd b c"
  by sorry

lemma gcd_div_unit1: "is_unit a \<Longrightarrow> gcd (b div a) c = gcd b c"
  by sorry

lemma gcd_div_unit2: "is_unit a \<Longrightarrow> gcd b (c div a) = gcd b c"
  by sorry

lemma normalize_gcd_left: "gcd (normalize a) b = gcd a b"
  by sorry

lemma normalize_gcd_right: "gcd a (normalize b) = gcd a b"
  by sorry

lemma gcd_add1 [simp]: "gcd (m + n) n = gcd m n"
  by sorry

lemma gcd_add2 [simp]: "gcd m (m + n) = gcd m n"
  by sorry

lemma gcd_add_mult: "gcd m (k * m + n) = gcd m n"
  by sorry

end

class ring_gcd = comm_ring_1 + semiring_gcd
begin

lemma gcd_neg1 [simp]: "gcd (-a) b = gcd a b"
  by sorry

lemma gcd_neg2 [simp]: "gcd a (-b) = gcd a b"
  by sorry

lemma gcd_neg_numeral_1 [simp]: "gcd (- numeral n) a = gcd (numeral n) a"
  by sorry

lemma gcd_neg_numeral_2 [simp]: "gcd a (- numeral n) = gcd a (numeral n)"
  by sorry

lemma gcd_diff1: "gcd (m - n) n = gcd m n"
  by sorry

lemma gcd_diff2: "gcd (n - m) n = gcd m n"
  by sorry

lemma lcm_neg1 [simp]: "lcm (-a) b = lcm a b"
  by sorry

lemma lcm_neg2 [simp]: "lcm a (-b) = lcm a b"
  by sorry

lemma lcm_neg_numeral_1 [simp]: "lcm (- numeral n) a = lcm (numeral n) a"
  by sorry

lemma lcm_neg_numeral_2 [simp]: "lcm a (- numeral n) = lcm a (numeral n)"
  by sorry

end

class semiring_Gcd = semiring_gcd + Gcd +
  assumes Gcd_dvd: "a \<in> A \<Longrightarrow> Gcd A dvd a"
    and Gcd_greatest: "(\<And>b. b \<in> A \<Longrightarrow> a dvd b) \<Longrightarrow> a dvd Gcd A"
    and normalize_Gcd [simp]: "normalize (Gcd A) = Gcd A"
  assumes dvd_Lcm: "a \<in> A \<Longrightarrow> a dvd Lcm A"
    and Lcm_least: "(\<And>b. b \<in> A \<Longrightarrow> b dvd a) \<Longrightarrow> Lcm A dvd a"
    and normalize_Lcm [simp]: "normalize (Lcm A) = Lcm A"
begin

lemma Lcm_Gcd: "Lcm A = Gcd {b. \<forall>a\<in>A. a dvd b}"
  by sorry

lemma Gcd_Lcm: "Gcd A = Lcm {b. \<forall>a\<in>A. b dvd a}"
  by sorry

lemma Gcd_empty [simp]: "Gcd {} = 0"
  by sorry

lemma Lcm_empty [simp]: "Lcm {} = 1"
  by sorry

lemma Gcd_insert [simp]: "Gcd (insert a A) = gcd a (Gcd A)"
  by sorry

lemma Lcm_insert [simp]: "Lcm (insert a A) = lcm a (Lcm A)"
  by sorry

lemma LcmI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> a dvd b"
    and "\<And>c. (\<And>a. a \<in> A \<Longrightarrow> a dvd c) \<Longrightarrow> b dvd c"
    and "normalize b = b"
  shows "b = Lcm A"
  by sorry

lemma Lcm_subset: "A \<subseteq> B \<Longrightarrow> Lcm A dvd Lcm B"
  by sorry

lemma Lcm_Un: "Lcm (A \<union> B) = lcm (Lcm A) (Lcm B)"
  by sorry

lemma Gcd_0_iff [simp]: "Gcd A = 0 \<longleftrightarrow> A \<subseteq> {0}"
  (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma Lcm_1_iff [simp]: "Lcm A = 1 \<longleftrightarrow> (\<forall>a\<in>A. is_unit a)"
  (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma unit_factor_Lcm: "unit_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)"
  by sorry

lemma unit_factor_Gcd: "unit_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
  by sorry

lemma GcdI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> b dvd a"
    and "\<And>c. (\<And>a. a \<in> A \<Longrightarrow> c dvd a) \<Longrightarrow> c dvd b"
    and "normalize b = b"
  shows "b = Gcd A"
  by sorry

lemma Gcd_eq_1_I:
  assumes "is_unit a" and "a \<in> A"
  shows "Gcd A = 1"
  by sorry

lemma Lcm_eq_0_I:
  assumes "0 \<in> A"
  shows "Lcm A = 0"
  by sorry

lemma Gcd_UNIV [simp]: "Gcd UNIV = 1"
  by sorry

lemma Lcm_UNIV [simp]: "Lcm UNIV = 0"
  by sorry

lemma Lcm_0_iff:
  assumes "finite A"
  shows "Lcm A = 0 \<longleftrightarrow> 0 \<in> A"
  by sorry

lemma Gcd_image_normalize [simp]: "Gcd (normalize ` A) = Gcd A"
  by sorry

lemma Gcd_eqI:
  assumes "normalize a = a"
  assumes "\<And>b. b \<in> A \<Longrightarrow> a dvd b"
    and "\<And>c. (\<And>b. b \<in> A \<Longrightarrow> c dvd b) \<Longrightarrow> c dvd a"
  shows "Gcd A = a"
  by sorry

lemma dvd_GcdD: "x dvd Gcd A \<Longrightarrow> y \<in> A \<Longrightarrow> x dvd y"
  by sorry

lemma dvd_Gcd_iff: "x dvd Gcd A \<longleftrightarrow> (\<forall>y\<in>A. x dvd y)"
  by sorry

lemma Gcd_mult: "Gcd ((*) c ` A) = normalize (c * Gcd A)"
  by sorry

lemma Lcm_eqI:
  assumes "normalize a = a"
    and "\<And>b. b \<in> A \<Longrightarrow> b dvd a"
    and "\<And>c. (\<And>b. b \<in> A \<Longrightarrow> b dvd c) \<Longrightarrow> a dvd c"
  shows "Lcm A = a"
  by sorry

lemma Lcm_dvdD: "Lcm A dvd x \<Longrightarrow> y \<in> A \<Longrightarrow> y dvd x"
  by sorry

lemma Lcm_dvd_iff: "Lcm A dvd x \<longleftrightarrow> (\<forall>y\<in>A. y dvd x)"
  by sorry

lemma Lcm_mult:
  assumes "A \<noteq> {}"
  shows "Lcm ((*) c ` A) = normalize (c * Lcm A)"
  by sorry

lemma Lcm_no_units: "Lcm A = Lcm (A - {a. is_unit a})"
  by sorry

lemma Lcm_0_iff': "Lcm A = 0 \<longleftrightarrow> (\<nexists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l))"
  by sorry

lemma Lcm_no_multiple: "(\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. \<not> a dvd m)) \<Longrightarrow> Lcm A = 0"
  by sorry

lemma Lcm_singleton [simp]: "Lcm {a} = normalize a"
  by sorry

lemma Lcm_2 [simp]: "Lcm {a, b} = lcm a b"
  by sorry

lemma Gcd_1: "1 \<in> A \<Longrightarrow> Gcd A = 1"
  by sorry

lemma Gcd_singleton [simp]: "Gcd {a} = normalize a"
  by sorry

lemma Gcd_2 [simp]: "Gcd {a, b} = gcd a b"
  by sorry

lemma Gcd_mono:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x dvd g x"
  shows   "(GCD x\<in>A. f x) dvd (GCD x\<in>A. g x)"
  by sorry

lemma Lcm_mono:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x dvd g x"
  shows   "(LCM x\<in>A. f x) dvd (LCM x\<in>A. g x)"
  by sorry

end


subsection \<open>An aside: GCD and LCM on finite sets for incomplete gcd rings\<close>

context semiring_gcd
begin

sublocale Gcd_fin: bounded_quasi_semilattice_set gcd 0 1 normalize
defines
  Gcd_fin (\<open>Gcd\<^sub>f\<^sub>i\<^sub>n\<close>) = "Gcd_fin.F :: 'a set \<Rightarrow> 'a" ..

abbreviation gcd_list :: "'a list \<Rightarrow> 'a"
  where "gcd_list xs \<equiv> Gcd\<^sub>f\<^sub>i\<^sub>n (set xs)"

sublocale Lcm_fin: bounded_quasi_semilattice_set lcm 1 0 normalize
defines
  Lcm_fin (\<open>Lcm\<^sub>f\<^sub>i\<^sub>n\<close>) = Lcm_fin.F ..

abbreviation lcm_list :: "'a list \<Rightarrow> 'a"
  where "lcm_list xs \<equiv> Lcm\<^sub>f\<^sub>i\<^sub>n (set xs)"

lemma Gcd_fin_dvd:
  "a \<in> A \<Longrightarrow> Gcd\<^sub>f\<^sub>i\<^sub>n A dvd a"
  by sorry

lemma dvd_Lcm_fin:
  "a \<in> A \<Longrightarrow> a dvd Lcm\<^sub>f\<^sub>i\<^sub>n A"
  by sorry

lemma Gcd_fin_greatest:
  "a dvd Gcd\<^sub>f\<^sub>i\<^sub>n A" if "finite A" and "\<And>b. b \<in> A \<Longrightarrow> a dvd b"
  by sorry

lemma Lcm_fin_least:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A dvd a" if "finite A" and "\<And>b. b \<in> A \<Longrightarrow> b dvd a"
  by sorry

lemma gcd_list_greatest:
  "a dvd gcd_list bs" if "\<And>b. b \<in> set bs \<Longrightarrow> a dvd b"
  by sorry

lemma lcm_list_least:
  "lcm_list bs dvd a" if "\<And>b. b \<in> set bs \<Longrightarrow> b dvd a"
  by sorry

lemma dvd_Gcd_fin_iff:
  "b dvd Gcd\<^sub>f\<^sub>i\<^sub>n A \<longleftrightarrow> (\<forall>a\<in>A. b dvd a)" if "finite A"
  by sorry

lemma dvd_gcd_list_iff:
  "b dvd gcd_list xs \<longleftrightarrow> (\<forall>a\<in>set xs. b dvd a)"
  by sorry

lemma Lcm_fin_dvd_iff:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A dvd b  \<longleftrightarrow> (\<forall>a\<in>A. a dvd b)" if "finite A"
  by sorry

lemma lcm_list_dvd_iff:
  "lcm_list xs dvd b  \<longleftrightarrow> (\<forall>a\<in>set xs. a dvd b)"
  by sorry

lemma Gcd_fin_mult:
  "Gcd\<^sub>f\<^sub>i\<^sub>n (image (times b) A) = normalize (b * Gcd\<^sub>f\<^sub>i\<^sub>n A)" if "finite A"
  by sorry

lemma Lcm_fin_mult:
  "Lcm\<^sub>f\<^sub>i\<^sub>n (image (times b) A) = normalize (b * Lcm\<^sub>f\<^sub>i\<^sub>n A)" if "A \<noteq> {}"
  by sorry
qed

lemma unit_factor_Gcd_fin:
  "unit_factor (Gcd\<^sub>f\<^sub>i\<^sub>n A) = of_bool (Gcd\<^sub>f\<^sub>i\<^sub>n A \<noteq> 0)"
  by sorry

lemma unit_factor_Lcm_fin:
  "unit_factor (Lcm\<^sub>f\<^sub>i\<^sub>n A) = of_bool (Lcm\<^sub>f\<^sub>i\<^sub>n A \<noteq> 0)"
  by sorry

lemma is_unit_Gcd_fin_iff [simp]:
  "is_unit (Gcd\<^sub>f\<^sub>i\<^sub>n A) \<longleftrightarrow> Gcd\<^sub>f\<^sub>i\<^sub>n A = 1"
  by sorry

lemma is_unit_Lcm_fin_iff [simp]:
  "is_unit (Lcm\<^sub>f\<^sub>i\<^sub>n A) \<longleftrightarrow> Lcm\<^sub>f\<^sub>i\<^sub>n A = 1"
  by sorry
 
lemma Gcd_fin_0_iff:
  "Gcd\<^sub>f\<^sub>i\<^sub>n A = 0 \<longleftrightarrow> A \<subseteq> {0} \<and> finite A"
  by sorry

lemma Lcm_fin_0_iff:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A = 0 \<longleftrightarrow> 0 \<in> A" if "finite A"
  by sorry

lemma Lcm_fin_1_iff:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A = 1 \<longleftrightarrow> (\<forall>a\<in>A. is_unit a) \<and> finite A"
  by sorry

end

context semiring_Gcd
begin

lemma Gcd_fin_eq_Gcd [simp]:
  "Gcd\<^sub>f\<^sub>i\<^sub>n A = Gcd A" if "finite A" for A :: "'a set"
  by sorry

lemma Gcd_set_eq_fold:
  "Gcd (set xs) = fold gcd xs 0"
  by sorry

lemma [code]:
  "Gcd (set xs) = Gcd\<^sub>f\<^sub>i\<^sub>n (set xs)"
  by sorry

lemma Lcm_fin_eq_Lcm [simp]:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A = Lcm A" if "finite A" for A :: "'a set"
  by sorry

lemma Lcm_set_eq_fold:
  "Lcm (set xs) = fold lcm xs 1"
  by sorry

lemma [code]:
  "Lcm (set xs) = Lcm\<^sub>f\<^sub>i\<^sub>n (set xs)"
  by sorry

end


subsection \<open>Coprimality\<close>

context semiring_gcd
begin

lemma coprime_imp_gcd_eq_1 [simp]:
  "gcd a b = 1" if "coprime a b"
  by sorry

lemma gcd_eq_1_imp_coprime [dest!]:
  "coprime a b" if "gcd a b = 1"
  by sorry

lemma coprime_iff_gcd_eq_1 [presburger, code]:
  "coprime a b \<longleftrightarrow> gcd a b = 1"
  by sorry

lemma is_unit_gcd [simp]:
  "is_unit (gcd a b) \<longleftrightarrow> coprime a b"
  by sorry

lemma coprime_add_one_left [simp]: "coprime (a + 1) a"
  by sorry

lemma coprime_add_one_right [simp]: "coprime a (a + 1)"
  by sorry

lemma coprime_mult_left_iff [simp]:
  "coprime (a * b) c \<longleftrightarrow> coprime a c \<and> coprime b c"
  by sorry

lemma coprime_mult_right_iff [simp]:
  "coprime c (a * b) \<longleftrightarrow> coprime c a \<and> coprime c b"
  by sorry

lemma coprime_power_left_iff [simp]:
  "coprime (a ^ n) b \<longleftrightarrow> coprime a b \<or> n = 0"
  by sorry

lemma coprime_power_right_iff [simp]:
  "coprime a (b ^ n) \<longleftrightarrow> coprime a b \<or> n = 0"
  by sorry

lemma prod_coprime_left:
  "coprime (\<Prod>i\<in>A. f i) a" if "\<And>i. i \<in> A \<Longrightarrow> coprime (f i) a"
  by sorry

lemma prod_coprime_right:
  "coprime a (\<Prod>i\<in>A. f i)" if "\<And>i. i \<in> A \<Longrightarrow> coprime a (f i)"
  by sorry

lemma prod_list_coprime_left:
  "coprime (prod_list xs) a" if "\<And>x. x \<in> set xs \<Longrightarrow> coprime x a"
  by sorry

lemma prod_list_coprime_right:
  "coprime a (prod_list xs)" if "\<And>x. x \<in> set xs \<Longrightarrow> coprime a x"
  by sorry

lemma coprime_dvd_mult_left_iff:
  "a dvd b * c \<longleftrightarrow> a dvd b" if "coprime a c"
  by sorry

lemma coprime_dvd_mult_right_iff:
  "a dvd c * b \<longleftrightarrow> a dvd b" if "coprime a c"
  by sorry

lemma divides_mult:
  "a * b dvd c" if "a dvd c" and "b dvd c" and "coprime a b"
  by sorry

lemma div_gcd_coprime:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "coprime (a div gcd a b) (b div gcd a b)"
  by sorry

lemma gcd_coprime:
  assumes c: "gcd a b \<noteq> 0"
    and a: "a = a' * gcd a b"
    and b: "b = b' * gcd a b"
  shows "coprime a' b'"
  by sorry

lemma gcd_coprime_exists:
  assumes "gcd a b \<noteq> 0"
  shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> coprime a' b'"
  by sorry

lemma pow_divides_pow_iff [simp]:
  "a ^ n dvd b ^ n \<longleftrightarrow> a dvd b" if "n > 0"
  by sorry

lemma coprime_crossproduct:
  fixes a b c d :: 'a
  assumes "coprime a d" and "coprime b c"
  shows "normalize a * normalize c = normalize b * normalize d \<longleftrightarrow>
    normalize a = normalize b \<and> normalize c = normalize d"
    (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma gcd_mult_left_left_cancel:
  "gcd (c * a) b = gcd a b" if "coprime b c"
  by sorry

lemma gcd_mult_left_right_cancel:
  "gcd (a * c) b = gcd a b" if "coprime b c"
  by sorry

lemma gcd_mult_right_left_cancel:
  "gcd a (c * b) = gcd a b" if "coprime a c"
  by sorry

lemma gcd_mult_right_right_cancel:
  "gcd a (b * c) = gcd a b" if "coprime a c"
  by sorry

lemma gcd_exp_weak:
  "gcd (a ^ n) (b ^ n) = normalize (gcd a b ^ n)"
  by sorry

lemma division_decomp:
  assumes "a dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
  by sorry

lemma lcm_coprime: "coprime a b \<Longrightarrow> lcm a b = normalize (a * b)"
  by sorry

end

context ring_gcd
begin

lemma coprime_minus_left_iff [simp]:
  "coprime (- a) b \<longleftrightarrow> coprime a b"
  by sorry

lemma coprime_minus_right_iff [simp]:
  "coprime a (- b) \<longleftrightarrow> coprime a b"
  by sorry

lemma coprime_diff_one_left [simp]: "coprime (a - 1) a"
  by sorry

lemma coprime_doff_one_right [simp]: "coprime a (a - 1)"
  by sorry

end

context semiring_Gcd
begin

lemma Lcm_coprime:
  assumes "finite A"
    and "A \<noteq> {}"
    and "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> coprime a b"
  shows "Lcm A = normalize (\<Prod>A)"
  by sorry

lemma Lcm_coprime':
  "card A \<noteq> 0 \<Longrightarrow>
    (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> coprime a b) \<Longrightarrow>
    Lcm A = normalize (\<Prod>A)"
  by sorry

end

text \<open>And some consequences: cancellation modulo @{term m}\<close>
lemma mult_mod_cancel_right:
  fixes m :: "'a::{euclidean_ring_cancel,semiring_gcd}"
  assumes eq: "(a * n) mod m = (b * n) mod m" and "coprime m n" 
  shows "a mod m = b mod m"
  by sorry

lemma mult_mod_cancel_left:
  fixes m :: "'a::{euclidean_ring_cancel,semiring_gcd}"
  assumes "(n * a) mod m = (n * b) mod m" and "coprime m n" 
  shows "a mod m = b mod m"
  by sorry


subsection \<open>GCD and LCM for multiplicative normalisation functions\<close>

class semiring_gcd_mult_normalize = semiring_gcd + normalization_semidom_multiplicative
begin

lemma mult_gcd_left: "c * gcd a b = unit_factor c * gcd (c * a) (c * b)"
  by sorry

lemma mult_gcd_right: "gcd a b * c = gcd (a * c) (b * c) * unit_factor c"
  by sorry

lemma gcd_mult_distrib': "normalize c * gcd a b = gcd (c * a) (c * b)"
  by sorry

lemma gcd_mult_distrib: "k * gcd a b = gcd (k * a) (k * b) * unit_factor k"
  by sorry

lemma gcd_mult_lcm [simp]: "gcd a b * lcm a b = normalize a * normalize b"
  by sorry

lemma lcm_mult_gcd [simp]: "lcm a b * gcd a b = normalize a * normalize b"
  by sorry

lemma mult_lcm_left: "c * lcm a b = unit_factor c * lcm (c * a) (c * b)"
  by sorry

lemma mult_lcm_right: "lcm a b * c = lcm (a * c) (b * c) * unit_factor c"
  by sorry

lemma lcm_gcd_prod: "lcm a b * gcd a b = normalize (a * b)"
  by sorry

lemma lcm_mult_distrib': "normalize c * lcm a b = lcm (c * a) (c * b)"
  by sorry

lemma lcm_mult_distrib: "k * lcm a b = lcm (k * a) (k * b) * unit_factor k"
  by sorry

lemma coprime_crossproduct':
  fixes a b c d
  assumes "b \<noteq> 0"
  assumes unit_factors: "unit_factor b = unit_factor d"
  assumes coprime: "coprime a b" "coprime c d"
  shows "a * d = b * c \<longleftrightarrow> a = c \<and> b = d"
  by sorry

lemma gcd_exp [simp]:
  "gcd (a ^ n) (b ^ n) = gcd a b ^ n"
  by sorry

end


subsection \<open>GCD and LCM on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

instantiation nat :: gcd
begin

fun gcd_nat  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gcd_nat x y = (if y = 0 then x else gcd y (x mod y))"

definition lcm_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "lcm_nat x y = x * y div (gcd x y)"

instance ..

end

instantiation int :: gcd
begin

definition gcd_int  :: "int \<Rightarrow> int \<Rightarrow> int"
  where "gcd_int x y = int (gcd (nat \<bar>x\<bar>) (nat \<bar>y\<bar>))"

definition lcm_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "lcm_int x y = int (lcm (nat \<bar>x\<bar>) (nat \<bar>y\<bar>))"

instance ..

end

lemma gcd_int_int_eq [simp]:
  "gcd (int m) (int n) = int (gcd m n)"
  by sorry

lemma gcd_nat_abs_left_eq [simp]:
  "gcd (nat \<bar>k\<bar>) n = nat (gcd k (int n))"
  by sorry

lemma gcd_nat_abs_right_eq [simp]:
  "gcd n (nat \<bar>k\<bar>) = nat (gcd (int n) k)"
  by sorry

lemma abs_gcd_int [simp]:
  "\<bar>gcd x y\<bar> = gcd x y"
  for x y :: int
  by sorry

lemma gcd_abs1_int [simp]:
  "gcd \<bar>x\<bar> y = gcd x y"
  for x y :: int
  by sorry

lemma gcd_abs2_int [simp]:
  "gcd x \<bar>y\<bar> = gcd x y"
  for x y :: int
  by sorry

lemma lcm_int_int_eq [simp]:
  "lcm (int m) (int n) = int (lcm m n)"
  by sorry

lemma lcm_nat_abs_left_eq [simp]:
  "lcm (nat \<bar>k\<bar>) n = nat (lcm k (int n))"
  by sorry

lemma lcm_nat_abs_right_eq [simp]:
  "lcm n (nat \<bar>k\<bar>) = nat (lcm (int n) k)"
  by sorry

lemma lcm_abs1_int [simp]:
  "lcm \<bar>x\<bar> y = lcm x y"
  for x y :: int
  by sorry

lemma lcm_abs2_int [simp]:
  "lcm x \<bar>y\<bar> = lcm x y"
  for x y :: int
  by sorry

lemma abs_lcm_int [simp]: "\<bar>lcm i j\<bar> = lcm i j"
  for i j :: int
  by sorry

lemma gcd_nat_induct [case_names base step]:
  fixes m n :: nat
  assumes "\<And>m. P m 0"
    and "\<And>m n. 0 < n \<Longrightarrow> P n (m mod n) \<Longrightarrow> P m n"
  shows "P m n"
  by sorry

lemma gcd_neg1_int [simp]: "gcd (- x) y = gcd x y"
  for x y :: int
  by sorry

lemma gcd_neg2_int [simp]: "gcd x (- y) = gcd x y"
  for x y :: int
  by sorry

lemma gcd_cases_int:
  fixes x y :: int
  assumes "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (gcd x y)"
    and "x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (gcd x (- y))"
    and "x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (gcd (- x) y)"
    and "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (gcd (- x) (- y))"
  shows "P (gcd x y)"
  by sorry

lemma gcd_ge_0_int [simp]: "gcd (x::int) y >= 0"
  for x y :: int
  by sorry

lemma lcm_neg1_int: "lcm (- x) y = lcm x y"
  for x y :: int
  by sorry

lemma lcm_neg2_int: "lcm x (- y) = lcm x y"
  for x y :: int
  by sorry

lemma lcm_cases_int:
  fixes x y :: int
  assumes "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (lcm x y)"
    and "x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (lcm x (- y))"
    and "x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (lcm (- x) y)"
    and "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (lcm (- x) (- y))"
  shows "P (lcm x y)"
  by sorry

lemma lcm_ge_0_int [simp]: "lcm x y \<ge> 0"
  for x y :: int
  by sorry

lemma gcd_0_nat: "gcd x 0 = x"
  for x :: nat
  by sorry

lemma gcd_0_int [simp]: "gcd x 0 = \<bar>x\<bar>"
  for x :: int
  by sorry

lemma gcd_0_left_nat: "gcd 0 x = x"
  for x :: nat
  by sorry

lemma gcd_0_left_int [simp]: "gcd 0 x = \<bar>x\<bar>"
  for x :: int
  by sorry

lemma gcd_red_nat: "gcd x y = gcd y (x mod y)"
  for x y :: nat
  by sorry


text \<open>Weaker, but useful for the simplifier.\<close>

lemma gcd_non_0_nat: "y \<noteq> 0 \<Longrightarrow> gcd x y = gcd y (x mod y)"
  for x y :: nat
  by sorry

lemma gcd_1_nat [simp]: "gcd m 1 = 1"
  for m :: nat
  by sorry

lemma gcd_Suc_0 [simp]: "gcd m (Suc 0) = Suc 0"
  for m :: nat
  by sorry

lemma gcd_1_int [simp]: "gcd m 1 = 1"
  for m :: int
  by sorry

lemma gcd_idem_nat: "gcd x x = x"
  for x :: nat
  by sorry

lemma gcd_idem_int: "gcd x x = \<bar>x\<bar>"
  for x :: int
  by sorry

declare gcd_nat.simps [simp del]

text \<open>
  \<^medskip> \<^term>\<open>gcd m n\<close> divides \<open>m\<close> and \<open>n\<close>.
  The conjunctions don't seem provable separately.
\<close>

instance nat :: semiring_gcd
proof
  fix m n :: nat
  show "gcd m n dvd m" and "gcd m n dvd n"
  proof (induct m n rule: gcd_nat_induct)
    case (step m n)
    then have "gcd n (m mod n) dvd m"
      by (metis dvd_mod_imp_dvd)
    with step show "gcd m n dvd m"
      by (simp add: gcd_non_0_nat)
  qed (simp_all add: gcd_0_nat gcd_non_0_nat)
next
  fix m n k :: nat
  assume "k dvd m" and "k dvd n"
  then show "k dvd gcd m n"
    by (induct m n rule: gcd_nat_induct) (simp_all add: gcd_non_0_nat dvd_mod gcd_0_nat)
qed (simp_all add: lcm_nat_def)

instance int :: ring_gcd
proof
  fix k l r :: int
  show [simp]: "gcd k l dvd k" "gcd k l dvd l"
    using gcd_dvd1 [of "nat \<bar>k\<bar>" "nat \<bar>l\<bar>"]
      gcd_dvd2 [of "nat \<bar>k\<bar>" "nat \<bar>l\<bar>"]
    by simp_all
  show "lcm k l = normalize (k * l div gcd k l)"
    using lcm_gcd [of "nat \<bar>k\<bar>" "nat \<bar>l\<bar>"]
    by (simp add: nat_eq_iff of_nat_div abs_mult abs_div)
  assume "r dvd k" "r dvd l"
  then show "r dvd gcd k l"
    using gcd_greatest [of "nat \<bar>r\<bar>" "nat \<bar>k\<bar>" "nat \<bar>l\<bar>"]
    by simp
qed simp

lemma gcd_le1_nat [simp]: "a \<noteq> 0 \<Longrightarrow> gcd a b \<le> a"
  for a b :: nat
  by sorry

lemma gcd_le2_nat [simp]: "b \<noteq> 0 \<Longrightarrow> gcd a b \<le> b"
  for a b :: nat
  by sorry

lemma gcd_le1_int [simp]: "a > 0 \<Longrightarrow> gcd a b \<le> a"
  for a b :: int
  by sorry

lemma gcd_le2_int [simp]: "b > 0 \<Longrightarrow> gcd a b \<le> b"
  for a b :: int
  by sorry

lemma gcd_pos_nat [simp]: "gcd m n > 0 \<longleftrightarrow> m \<noteq> 0 \<or> n \<noteq> 0"
  for m n :: nat
  by sorry

lemma gcd_pos_int [simp]: "gcd m n > 0 \<longleftrightarrow> m \<noteq> 0 \<or> n \<noteq> 0"
  for m n :: int
  by sorry

lemma gcd_unique_nat: "d dvd a \<and> d dvd b \<and> (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  for d a :: nat
  by sorry

lemma gcd_unique_int:
  "d \<ge> 0 \<and> d dvd a \<and> d dvd b \<and> (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  for d a :: int
  by sorry

interpretation gcd_nat:
  semilattice_neutr_order gcd "0::nat" Rings.dvd "\<lambda>m n. m dvd n \<and> m \<noteq> n"
  by standard (auto simp: gcd_unique_nat [symmetric] intro: dvd_antisym dvd_trans)

lemma gcd_proj1_if_dvd_int [simp]: "x dvd y \<Longrightarrow> gcd x y = \<bar>x\<bar>"
  for x y :: int
  by sorry

lemma gcd_proj2_if_dvd_int [simp]: "y dvd x \<Longrightarrow> gcd x y = \<bar>y\<bar>"
  for x y :: int
  by sorry


text \<open>\<^medskip> Multiplication laws.\<close>

lemma gcd_mult_distrib_nat: "k * gcd m n = gcd (k * m) (k * n)"
  for k m n :: nat
  \<comment> \<open>\<^cite>\<open>\<open>page 27\<close> in davenport92\<close>\<close>
  by sorry

lemma gcd_mult_distrib_int: "\<bar>k\<bar> * gcd m n = gcd (k * m) (k * n)"
  for k m n :: int
  by sorry

text \<open>\medskip Addition laws.\<close>

(* TODO: add the other variations? *)

lemma gcd_diff1_nat: "m \<ge> n \<Longrightarrow> gcd (m - n) n = gcd m n"
  for m n :: nat
  by sorry

lemma gcd_diff2_nat: "n \<ge> m \<Longrightarrow> gcd (n - m) n = gcd m n"
  for m n :: nat
  by sorry

lemma gcd_non_0_int: 
  fixes x y :: int
  assumes "y > 0" shows "gcd x y = gcd y (x mod y)"
  by sorry

lemma gcd_red_int: "gcd x y = gcd y (x mod y)"
  for x y :: int
  by sorry

(* TODO: differences, and all variations of addition rules
    as simplification rules for nat and int *)

(* TODO: add the three variations of these, and for ints? *)

lemma finite_divisors_nat [simp]: (* FIXME move *)
  fixes m :: nat
  assumes "m > 0"
  shows "finite {d. d dvd m}"
  by sorry

lemma finite_divisors_int [simp]:
  fixes i :: int
  assumes "i \<noteq> 0"
  shows "finite {d. d dvd i}"
  by sorry

lemma Max_divisors_self_nat [simp]: "n \<noteq> 0 \<Longrightarrow> Max {d::nat. d dvd n} = n"
  by sorry

lemma Max_divisors_self_int [simp]: 
  assumes "n \<noteq> 0" shows "Max {d::int. d dvd n} = \<bar>n\<bar>"
  by sorry

lemma gcd_is_Max_divisors_nat:
  fixes m n :: nat
  assumes "n > 0" shows "gcd m n = Max {d. d dvd m \<and> d dvd n}"
  by sorry

lemma gcd_is_Max_divisors_int:
  fixes m n :: int
  assumes "n \<noteq> 0" shows "gcd m n = Max {d. d dvd m \<and> d dvd n}"
  by sorry

lemma gcd_code_int [code]: "gcd k l = \<bar>if l = 0 then k else gcd l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  for k l :: int
  by sorry

lemma coprime_Suc_left_nat [simp]:
  "coprime (Suc n) n"
  by sorry

lemma coprime_Suc_right_nat [simp]:
  "coprime n (Suc n)"
  by sorry

lemma coprime_diff_one_left_nat [simp]:
  "coprime (n - 1) n" if "n > 0" for n :: nat
  by sorry

lemma coprime_diff_one_right_nat [simp]:
  "coprime n (n - 1)" if "n > 0" for n :: nat
  by sorry

lemma coprime_crossproduct_nat:
  fixes a b c d :: nat
  assumes "coprime a d" and "coprime b c"
  shows "a * c = b * d \<longleftrightarrow> a = b \<and> c = d"
  by sorry

lemma coprime_crossproduct_int:
  fixes a b c d :: int
  assumes "coprime a d" and "coprime b c"
  shows "\<bar>a\<bar> * \<bar>c\<bar> = \<bar>b\<bar> * \<bar>d\<bar> \<longleftrightarrow> \<bar>a\<bar> = \<bar>b\<bar> \<and> \<bar>c\<bar> = \<bar>d\<bar>"
  by sorry


subsection \<open>Bezout's theorem\<close>

text \<open>
  Function \<open>bezw\<close> returns a pair of witnesses to Bezout's theorem --
  see the theorems that follow the definition.
\<close>

fun bezw :: "nat \<Rightarrow> nat \<Rightarrow> int * int"
  where "bezw x y =
    (if y = 0 then (1, 0)
     else
      (snd (bezw y (x mod y)),
       fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * int(x div y)))"

lemma bezw_0 [simp]: "bezw x 0 = (1, 0)"
  by sorry

lemma bezw_non_0:
  "y > 0 \<Longrightarrow> bezw x y =
    (snd (bezw y (x mod y)), fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * int(x div y))"
  by sorry

declare bezw.simps [simp del]


lemma bezw_aux: "int (gcd x y) = fst (bezw x y) * int x + snd (bezw x y) * int y"
  by sorry


lemma bezout_int: "\<exists>u v. u * x + v * y = gcd x y"
  for x y :: int
  by sorry


text \<open>Versions of Bezout for \<open>nat\<close>, by Amine Chaieb.\<close>

lemma Euclid_induct [case_names swap zero add]:
  fixes P :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes c: "\<And>a b. P a b \<longleftrightarrow> P b a"
    and z: "\<And>a. P a 0"
    and add: "\<And>a b. P a b \<longrightarrow> P a (a + b)"
  shows "P a b"
  by sorry

lemma bezout_lemma_nat:
  fixes d::nat
  shows "\<lbrakk>d dvd a; d dvd b; a * x = b * y + d \<or> b * x = a * y + d\<rbrakk>
    \<Longrightarrow> \<exists>x y. d dvd a \<and> d dvd a + b \<and> (a * x = (a + b) * y + d \<or> (a + b) * x = a * y + d)"
  by sorry

lemma bezout_add_nat: 
  "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and> (a * x = b * y + d \<or> b * x = a * y + d)"
  by sorry

lemma bezout1_nat: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and> (a * x - b * y = d \<or> b * x - a * y = d)"
  by sorry

lemma bezout_add_strong_nat:
  fixes a b :: nat
  assumes a: "a \<noteq> 0"
  shows "\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d"
  by sorry

lemma bezout_nat:
  fixes a :: nat
  assumes a: "a \<noteq> 0"
  shows "\<exists>x y. a * x = b * y + gcd a b"
  by sorry


subsection \<open>LCM properties on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

lemma lcm_altdef_int [code]: "lcm a b = \<bar>a\<bar> * \<bar>b\<bar> div gcd a b"
  for a b :: int
  by sorry
  
lemma prod_gcd_lcm_nat: "m * n = gcd m n * lcm m n"
  for m n :: nat
  by sorry

lemma prod_gcd_lcm_int: "\<bar>m\<bar> * \<bar>n\<bar> = gcd m n * lcm m n"
  for m n :: int
  by sorry

lemma lcm_pos_nat: "m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> lcm m n > 0"
  for m n :: nat
  by sorry

lemma lcm_pos_int: "m \<noteq> 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> lcm m n > 0"
  for m n :: int
  by sorry

lemma dvd_pos_nat: "n > 0 \<Longrightarrow> m dvd n \<Longrightarrow> m > 0"  (* FIXME move *)
  for m n :: nat
  by sorry

lemma lcm_unique_nat:
  "a dvd d \<and> b dvd d \<and> (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  for a b d :: nat
  by sorry

lemma lcm_unique_int:
  "d \<ge> 0 \<and> a dvd d \<and> b dvd d \<and> (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  for a b d :: int
  by sorry

lemma lcm_proj2_if_dvd_nat [simp]: "x dvd y \<Longrightarrow> lcm x y = y"
  for x y :: nat
  by sorry

lemma lcm_proj2_if_dvd_int [simp]: "x dvd y \<Longrightarrow> lcm x y = \<bar>y\<bar>"
  for x y :: int
  by sorry

lemma lcm_proj1_if_dvd_nat [simp]: "x dvd y \<Longrightarrow> lcm y x = y"
  for x y :: nat
  by sorry

lemma lcm_proj1_if_dvd_int [simp]: "x dvd y \<Longrightarrow> lcm y x = \<bar>y\<bar>"
  for x y :: int
  by sorry

lemma lcm_proj1_iff_nat [simp]: "lcm m n = m \<longleftrightarrow> n dvd m"
  for m n :: nat
  by sorry

lemma lcm_proj2_iff_nat [simp]: "lcm m n = n \<longleftrightarrow> m dvd n"
  for m n :: nat
  by sorry

lemma lcm_proj1_iff_int [simp]: "lcm m n = \<bar>m\<bar> \<longleftrightarrow> n dvd m"
  for m n :: int
  by sorry

lemma lcm_proj2_iff_int [simp]: "lcm m n = \<bar>n\<bar> \<longleftrightarrow> m dvd n"
  for m n :: int
  by sorry

lemma lcm_1_iff_nat [simp]: "lcm m n = Suc 0 \<longleftrightarrow> m = Suc 0 \<and> n = Suc 0"
  for m n :: nat
  by sorry

lemma lcm_1_iff_int [simp]: "lcm m n = 1 \<longleftrightarrow> (m = 1 \<or> m = -1) \<and> (n = 1 \<or> n = -1)"
  for m n :: int
  by sorry


subsection \<open>The complete divisibility lattice on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

text \<open>
  Lifting \<open>gcd\<close> and \<open>lcm\<close> to sets (\<open>Gcd\<close> / \<open>Lcm\<close>).
  \<open>Gcd\<close> is defined via \<open>Lcm\<close> to facilitate the proof that we have a complete lattice.
\<close>

instantiation nat :: semiring_Gcd
begin

interpretation semilattice_neutr_set lcm "1::nat"
  by standard simp_all

definition "Lcm M = (if finite M then F M else 0)" for M :: "nat set"

lemma Lcm_nat_empty: "Lcm {} = (1::nat)"
  by sorry

lemma Lcm_nat_insert: "Lcm (insert n M) = lcm n (Lcm M)" for n :: nat
  by sorry

lemma Lcm_nat_infinite: "infinite M \<Longrightarrow> Lcm M = 0" for M :: "nat set"
  by sorry

lemma dvd_Lcm_nat [simp]:
  fixes M :: "nat set"
  assumes "m \<in> M"
  shows "m dvd Lcm M"
  by sorry

lemma Lcm_dvd_nat [simp]:
  fixes M :: "nat set"
  assumes "\<forall>m\<in>M. m dvd n"
  shows "Lcm M dvd n"
  by sorry

definition "Gcd M = Lcm {d. \<forall>m\<in>M. d dvd m}" for M :: "nat set"

instance
proof
  fix N :: "nat set"
  fix n :: nat
  show "Gcd N dvd n" if "n \<in> N"
    using that by (induct N rule: infinite_finite_induct) (auto simp: Gcd_nat_def)
  show "n dvd Gcd N" if "\<And>m. m \<in> N \<Longrightarrow> n dvd m"
    using that by (induct N rule: infinite_finite_induct) (auto simp: Gcd_nat_def)
  show "n dvd Lcm N" if "n \<in> N"
    using that by (induct N rule: infinite_finite_induct) auto
  show "Lcm N dvd n" if "\<And>m. m \<in> N \<Longrightarrow> m dvd n"
    using that by (induct N rule: infinite_finite_induct) auto
  show "normalize (Gcd N) = Gcd N" and "normalize (Lcm N) = Lcm N"
    by simp_all
qed

end

lemma Gcd_nat_eq_one: "1 \<in> N \<Longrightarrow> Gcd N = 1"
  for N :: "nat set"
  by sorry

instance nat :: semiring_gcd_mult_normalize
  by intro_classes (auto simp: unit_factor_nat_def)


text \<open>Alternative characterizations of Gcd:\<close>

lemma Gcd_eq_Max:
  fixes M :: "nat set"
  assumes "finite (M::nat set)" and "M \<noteq> {}" and "0 \<notin> M"
  shows "Gcd M = Max (\<Inter>m\<in>M. {d. d dvd m})"
  by sorry

lemma Gcd_remove0_nat: "Gcd M = Gcd (M - {0})"
  for M :: "nat set"
  by sorry

lemma Lcm_in_lcm_closed_set_nat:
  fixes M :: "nat set" 
  assumes "finite M" "M \<noteq> {}" "\<And>m n. \<lbrakk>m \<in> M; n \<in> M\<rbrakk> \<Longrightarrow> lcm m n \<in> M"
  shows "Lcm M \<in> M"
  by sorry

lemma Lcm_eq_Max_nat:
  fixes M :: "nat set" 
  assumes M: "finite M" "M \<noteq> {}" "0 \<notin> M" and lcm: "\<And>m n. \<lbrakk>m \<in> M; n \<in> M\<rbrakk> \<Longrightarrow> lcm m n \<in> M"
  shows "Lcm M = Max M"
  by sorry

lemma mult_inj_if_coprime_nat:
  "inj_on f A \<Longrightarrow> inj_on g B \<Longrightarrow> (\<And>a b. \<lbrakk>a\<in>A; b\<in>B\<rbrakk> \<Longrightarrow> coprime (f a) (g b)) \<Longrightarrow>
    inj_on (\<lambda>(a, b). f a * g b) (A \<times> B)"
  for f :: "'a \<Rightarrow> nat" and g :: "'b \<Rightarrow> nat"
  by sorry


subsubsection \<open>Setwise GCD and LCM for integers\<close>

instantiation int :: Gcd
begin

definition Gcd_int :: "int set \<Rightarrow> int"
  where "Gcd K = int (GCD k\<in>K. (nat \<circ> abs) k)"

definition Lcm_int :: "int set \<Rightarrow> int"
  where "Lcm K = int (LCM k\<in>K. (nat \<circ> abs) k)"

instance ..

end

lemma Gcd_int_eq [simp]:
  "(GCD n\<in>N. int n) = int (Gcd N)"
  by sorry

lemma Gcd_nat_abs_eq [simp]:
  "(GCD k\<in>K. nat \<bar>k\<bar>) = nat (Gcd K)"
  by sorry

lemma abs_Gcd_eq [simp]:
  "\<bar>Gcd K\<bar> = Gcd K" for K :: "int set"
  by sorry

lemma uminus_Gcd_eq [simp]: 
  fixes K::"int set"
  shows "Gcd (uminus ` K) = Gcd K"
  by sorry

lemma Gcd_int_greater_eq_0 [simp]:
  "Gcd K \<ge> 0"
  for K :: "int set"
  by sorry

lemma Gcd_abs_eq [simp]:
  "(GCD k\<in>K. \<bar>k\<bar>) = Gcd K"
  for K :: "int set"
  by sorry

lemma Lcm_int_eq [simp]:
  "(LCM n\<in>N. int n) = int (Lcm N)"
  by sorry

lemma Lcm_nat_abs_eq [simp]:
  "(LCM k\<in>K. nat \<bar>k\<bar>) = nat (Lcm K)"
  by sorry

lemma abs_Lcm_eq [simp]:
  "\<bar>Lcm K\<bar> = Lcm K" for K :: "int set"
  by sorry

lemma Lcm_int_greater_eq_0 [simp]:
  "Lcm K \<ge> 0"
  for K :: "int set"
  by sorry

lemma Lcm_abs_eq [simp]:
  "(LCM k\<in>K. \<bar>k\<bar>) = Lcm K"
  for K :: "int set"
  by sorry

instance int :: semiring_Gcd
proof
  fix K :: "int set" and k :: int
  show "Gcd K dvd k" and "k dvd Lcm K" if "k \<in> K"
    using that Gcd_dvd [of "nat \<bar>k\<bar>" "(nat \<circ> abs) ` K"]
      dvd_Lcm [of "nat \<bar>k\<bar>" "(nat \<circ> abs) ` K"]
    by (simp_all add: comp_def)
  show "k dvd Gcd K" if "\<And>l. l \<in> K \<Longrightarrow> k dvd l"
  proof -
    have "nat \<bar>k\<bar> dvd (GCD k\<in>K. nat \<bar>k\<bar>)"
      by (rule Gcd_greatest) (use that in auto)
    then show ?thesis by simp
  qed
  show "Lcm K dvd k" if "\<And>l. l \<in> K \<Longrightarrow> l dvd k"
  proof -
    have "(LCM k\<in>K. nat \<bar>k\<bar>) dvd nat \<bar>k\<bar>"
      by (rule Lcm_least) (use that in auto)
    then show ?thesis by simp
  qed
qed (simp_all add: sgn_mult)

instance int :: semiring_gcd_mult_normalize
  by intro_classes (auto simp: sgn_mult)


subsection \<open>GCD and LCM on \<^typ>\<open>integer\<close>\<close>

instantiation integer :: gcd
begin

context
  includes integer.lifting
begin

lift_definition gcd_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is gcd .

lift_definition lcm_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is lcm .

end

instance ..

end

lifting_update integer.lifting
lifting_forget integer.lifting

context
  includes integer.lifting
begin

lemma gcd_code_integer [code]: "gcd k l = \<bar>if l = (0::integer) then k else gcd l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  by sorry

lemma lcm_code_integer [code]: "lcm a b = \<bar>a\<bar> * \<bar>b\<bar> div gcd a b"
  for a b :: integer
  by sorry

end

code_printing
  constant "gcd :: integer \<Rightarrow> _" \<rightharpoonup>
    (OCaml) "!(fun k l -> if Z.equal k Z.zero then/ Z.abs l else if Z.equal/ l Z.zero then Z.abs k else Z.gcd k l)"
  and (Haskell) "Prelude.gcd"
  and (Scala) "_.gcd'((_)')"
  \<comment> \<open>There is no gcd operation in the SML standard library, so no code setup for SML\<close>

text \<open>Some code equations\<close>

lemmas Gcd_nat_set_eq_fold [code] = Gcd_set_eq_fold [where ?'a = nat]
lemmas Lcm_nat_set_eq_fold [code] = Lcm_set_eq_fold [where ?'a = nat]
lemmas Gcd_int_set_eq_fold [code] = Gcd_set_eq_fold [where ?'a = int]
lemmas Lcm_int_set_eq_fold [code] = Lcm_set_eq_fold [where ?'a = int]

text \<open>Fact aliases.\<close>

lemma lcm_0_iff_nat [simp]: "lcm m n = 0 \<longleftrightarrow> m = 0 \<or> n = 0"
  for m n :: nat
  by sorry

lemma lcm_0_iff_int [simp]: "lcm m n = 0 \<longleftrightarrow> m = 0 \<or> n = 0"
  for m n :: int
  by sorry

lemma dvd_lcm_I1_nat [simp]: "k dvd m \<Longrightarrow> k dvd lcm m n"
  for k m n :: nat
  by sorry

lemma dvd_lcm_I2_nat [simp]: "k dvd n \<Longrightarrow> k dvd lcm m n"
  for k m n :: nat
  by sorry

lemma dvd_lcm_I1_int [simp]: "i dvd m \<Longrightarrow> i dvd lcm m n"
  for i m n :: int
  by sorry

lemma dvd_lcm_I2_int [simp]: "i dvd n \<Longrightarrow> i dvd lcm m n"
  for i m n :: int
  by sorry

lemmas Gcd_dvd_nat [simp] = Gcd_dvd [where ?'a = nat]
lemmas Gcd_dvd_int [simp] = Gcd_dvd [where ?'a = int]
lemmas Gcd_greatest_nat [simp] = Gcd_greatest [where ?'a = nat]
lemmas Gcd_greatest_int [simp] = Gcd_greatest [where ?'a = int]

lemma dvd_Lcm_int [simp]: "m \<in> M \<Longrightarrow> m dvd Lcm M"
  for M :: "int set"
  by sorry

lemma gcd_neg_numeral_1_int [simp]: "gcd (- numeral n :: int) x = gcd (numeral n) x"
  by sorry

lemma gcd_neg_numeral_2_int [simp]: "gcd x (- numeral n :: int) = gcd x (numeral n)"
  by sorry

lemma gcd_proj1_if_dvd_nat [simp]: "x dvd y \<Longrightarrow> gcd x y = x"
  for x y :: nat
  by sorry

lemma gcd_proj2_if_dvd_nat [simp]: "y dvd x \<Longrightarrow> gcd x y = y"
  for x y :: nat
  by sorry

lemma Gcd_in:
  fixes A :: "nat set"
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> gcd a b \<in> A"
  assumes "A \<noteq> {}"
  shows   "Gcd A \<in> A"
  by sorry

lemma bezout_gcd_nat':
  fixes a b :: nat
  shows "\<exists>x y. b * y \<le> a * x \<and> a * x - b * y = gcd a b \<or> a * y \<le> b * x \<and> b * x - a * y = gcd a b"
  by sorry

lemmas Lcm_eq_0_I_nat [simp] = Lcm_eq_0_I [where ?'a = nat]
lemmas Lcm_0_iff_nat [simp] = Lcm_0_iff [where ?'a = nat]
lemmas Lcm_least_int [simp] = Lcm_least [where ?'a = int]


subsection \<open>Characteristic of a semiring\<close>

definition (in semiring_1) semiring_char :: "'a itself \<Rightarrow> nat" 
  where "semiring_char _ = Gcd {n. of_nat n = (0 :: 'a)}"

syntax "_type_char" :: "type => nat" (\<open>(\<open>indent=1 notation=\<open>mixfix CHAR\<close>\<close>CHAR/(1'(_')))\<close>)
syntax_consts "_type_char" \<rightleftharpoons> semiring_char
translations "CHAR('t)" \<rightharpoonup> "CONST semiring_char (CONST Pure.type :: 't itself)"
print_translation \<open>
  let
    fun char_type_tr' ctxt [Const (\<^const_syntax>\<open>Pure.type\<close>, Type (_, [T]))] =
      Syntax.const \<^syntax_const>\<open>_type_char\<close> $ Syntax_Phases.term_of_typ ctxt T
  in [(\<^const_syntax>\<open>semiring_char\<close>, char_type_tr')] end
\<close>

context semiring_1
begin

lemma of_nat_CHAR [simp]: "of_nat CHAR('a) = (0 :: 'a)"
  by sorry

lemma of_nat_eq_0_iff_char_dvd: "of_nat n = (0 :: 'a) \<longleftrightarrow> CHAR('a) dvd n"
  by sorry

lemma CHAR_eqI:
  assumes "of_nat c = (0 :: 'a)"
  assumes "\<And>x. of_nat x = (0 :: 'a) \<Longrightarrow> c dvd x"
  shows   "CHAR('a) = c"
  by sorry

lemma CHAR_eq0_iff: "CHAR('a) = 0 \<longleftrightarrow> (\<forall>n>0. of_nat n \<noteq> (0::'a))"
  by sorry

lemma CHAR_pos_iff: "CHAR('a) > 0 \<longleftrightarrow> (\<exists>n>0. of_nat n = (0::'a))"
  by sorry

lemma CHAR_eq_posI:
  assumes "c > 0" "of_nat c = (0 :: 'a)" "\<And>x. x > 0 \<Longrightarrow> x < c \<Longrightarrow> of_nat x \<noteq> (0 :: 'a)"
  shows   "CHAR('a) = c"
  by sorry

end

lemma (in semiring_char_0) CHAR_eq_0 [simp]: "CHAR('a) = 0"
  by sorry


lemma CHAR_not_1 [simp]: "CHAR('a :: {semiring_1, zero_neq_one}) \<noteq> Suc 0"
  by sorry

lemma (in idom) CHAR_not_1' [simp]: "CHAR('a) \<noteq> Suc 0"
  by sorry

lemma (in ring_1) uminus_CHAR_2:
  assumes "CHAR('a) = 2"
  shows   "-(x :: 'a) = x"
  by sorry

lemma (in ring_1) minus_CHAR_2:
  assumes "CHAR('a) = 2"
  shows   "(x - y :: 'a) = x + y"
  by sorry

lemma (in semiring_1_cancel) of_nat_eq_iff_char_dvd:
  assumes "m < n"
  shows   "of_nat m = (of_nat n :: 'a) \<longleftrightarrow> CHAR('a) dvd (n - m)"
  by sorry

lemma (in ring_1) of_int_eq_0_iff_char_dvd:
  "(of_int n = (0 :: 'a)) = (int CHAR('a) dvd n)"
  by sorry

lemma (in semiring_1_cancel) finite_imp_CHAR_pos:
  assumes "finite (UNIV :: 'a set)"
  shows   "CHAR('a) > 0"
  by sorry

end
