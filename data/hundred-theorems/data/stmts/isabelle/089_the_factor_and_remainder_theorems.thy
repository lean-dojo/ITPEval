(*  Title:      HOL/Computational_Algebra/Polynomial.thy
    Author:     Brian Huffman
    Author:     Clemens Ballarin
    Author:     Amine Chaieb
    Author:     Florian Haftmann
*)

section \<open>Polynomials as type over a ring structure\<close>

theory Polynomial
imports
  Complex_Main
  "HOL-Library.More_List"
  "HOL-Library.Infinite_Set"
  Primes
begin

context semidom_modulo
begin

lemma not_dvd_imp_mod_neq_0:
  \<open>a mod b \<noteq> 0\<close> if \<open>\<not> b dvd a\<close>
  by sorry

end

subsection \<open>Auxiliary: operations for lists (later) representing coefficients\<close>

definition cCons :: "'a::zero \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixr \<open>##\<close> 65)
  where "x ## xs = (if xs = [] \<and> x = 0 then [] else x # xs)"

lemma cCons_0_Nil_eq [simp]: "0 ## [] = []"
  by sorry

lemma cCons_Cons_eq [simp]: "x ## y # ys = x # y # ys"
  by sorry

lemma cCons_append_Cons_eq [simp]: "x ## xs @ y # ys = x # xs @ y # ys"
  by sorry

lemma cCons_not_0_eq [simp]: "x \<noteq> 0 \<Longrightarrow> x ## xs = x # xs"
  by sorry

lemma strip_while_not_0_Cons_eq [simp]:
  "strip_while (\<lambda>x. x = 0) (x # xs) = x ## strip_while (\<lambda>x. x = 0) xs"
  by sorry

lemma tl_cCons [simp]: "tl (x ## xs) = xs"
  by sorry


subsection \<open>Definition of type \<open>poly\<close>\<close>

typedef (overloaded) 'a poly = "{f :: nat \<Rightarrow> 'a::zero. \<forall>\<^sub>\<infinity> n. f n = 0}"
  morphisms coeff Abs_poly
  by (auto intro!: ALL_MOST)

setup_lifting type_definition_poly

lemma poly_eq_iff: "p = q \<longleftrightarrow> (\<forall>n. coeff p n = coeff q n)"
  by sorry

lemma poly_eqI: "(\<And>n. coeff p n = coeff q n) \<Longrightarrow> p = q"
  by sorry

lemma MOST_coeff_eq_0: "\<forall>\<^sub>\<infinity> n. coeff p n = 0"
  by sorry

lemma coeff_Abs_poly:
  assumes "\<And>i. i > n \<Longrightarrow> f i = 0"
  shows   "coeff (Abs_poly f) = f"
  by sorry


subsection \<open>Degree of a polynomial\<close>

definition degree :: "'a::zero poly \<Rightarrow> nat"
  where "degree p = (LEAST n. \<forall>i>n. coeff p i = 0)"

lemma degree_cong:
  assumes "\<And>i. coeff p i = 0 \<longleftrightarrow> coeff q i = 0"
  shows   "degree p = degree q"
  by sorry

lemma coeff_Abs_poly_If_le:
  "coeff (Abs_poly (\<lambda>i. if i \<le> n then f i else 0)) = (\<lambda>i. if i \<le> n then f i else 0)"
  by sorry

lemma coeff_eq_0:
  assumes "degree p < n"
  shows "coeff p n = 0"
  by sorry

lemma le_degree: "coeff p n \<noteq> 0 \<Longrightarrow> n \<le> degree p"
  by sorry

lemma degree_le: "\<forall>i>n. coeff p i = 0 \<Longrightarrow> degree p \<le> n"
  by sorry

lemma less_degree_imp: "n < degree p \<Longrightarrow> \<exists>i>n. coeff p i \<noteq> 0"
  by sorry

lemma poly_eqI2:
  assumes "degree p = degree q" and "\<And>i. i \<le> degree p \<Longrightarrow> coeff p i = coeff q i"
  shows "p = q"
  by sorry


subsection \<open>The zero polynomial\<close>

instantiation poly :: (zero) zero
begin

lift_definition zero_poly :: "'a poly"
  is "\<lambda>_. 0"
  by (rule MOST_I) simp

instance ..

end

lemma coeff_0 [simp]: "coeff 0 n = 0"
  by sorry

lemma degree_0 [simp]: "degree 0 = 0"
  by sorry

lemma leading_coeff_neq_0:
  assumes "p \<noteq> 0"
  shows "coeff p (degree p) \<noteq> 0"
  by sorry

lemma leading_coeff_0_iff [simp]: "coeff p (degree p) = 0 \<longleftrightarrow> p = 0"
  by sorry

lemma degree_lessI:
  assumes "p \<noteq> 0 \<or> n > 0" "\<forall>k\<ge>n. coeff p k = 0"
  shows   "degree p < n"
  by sorry

lemma eq_zero_or_degree_less:            
  assumes "degree p \<le> n" and "coeff p n = 0"
  shows "p = 0 \<or> degree p < n"
  by sorry

lemma coeff_0_degree_minus_1: "coeff rrr dr = 0 \<Longrightarrow> degree rrr \<le> dr \<Longrightarrow> degree rrr \<le> dr - 1"
  by sorry


subsection \<open>List-style constructor for polynomials\<close>

lift_definition pCons :: "'a::zero \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p. case_nat a (coeff p)"
  by (rule MOST_SucD) (simp add: MOST_coeff_eq_0)

lemmas coeff_pCons = pCons.rep_eq

lemma coeff_pCons': "poly.coeff (pCons c p) n = (if n = 0 then c else poly.coeff p (n - 1))"
  by sorry

lemma coeff_pCons_0 [simp]: "coeff (pCons a p) 0 = a"
  by sorry

lemma coeff_pCons_Suc [simp]: "coeff (pCons a p) (Suc n) = coeff p n"
  by sorry

lemma degree_pCons_le: "degree (pCons a p) \<le> Suc (degree p)"
  by sorry

lemma degree_pCons_eq: "p \<noteq> 0 \<Longrightarrow> degree (pCons a p) = Suc (degree p)"
  by sorry

lemma degree_pCons_0: "degree (pCons a 0) = 0"
  by sorry

lemma degree_pCons_eq_if [simp]: "degree (pCons a p) = (if p = 0 then 0 else Suc (degree p))"
  by sorry

lemma pCons_0_0 [simp]: "pCons 0 0 = 0"
  by sorry

lemma pCons_eq_iff [simp]: "pCons a p = pCons b q \<longleftrightarrow> a = b \<and> p = q"
  by sorry

lemma pCons_eq_0_iff [simp]: "pCons a p = 0 \<longleftrightarrow> a = 0 \<and> p = 0"
  by sorry

lemma pCons_cases [cases type: poly]:
  obtains (pCons) a q where "p = pCons a q"
  by sorry

lemma pCons_induct [case_names 0 pCons, induct type: poly]:
  assumes zero: "P 0"
  assumes pCons: "\<And>a p. a \<noteq> 0 \<or> p \<noteq> 0 \<Longrightarrow> P p \<Longrightarrow> P (pCons a p)"
  shows "P p"
  by sorry

lemma degree_eq_zeroE:
  fixes p :: "'a::zero poly"
  assumes "degree p = 0"
  obtains a where "p = pCons a 0"
  by sorry


subsection \<open>Quickcheck generator for polynomials\<close>

quickcheck_generator poly constructors: "0 :: _ poly", pCons


subsection \<open>List-style syntax for polynomials\<close>

syntax
  "_poly" :: "args \<Rightarrow> 'a poly"  (\<open>(\<open>indent=2 notation=\<open>mixfix polynomial enumeration\<close>\<close>[:_:])\<close>)
syntax_consts
  "_poly" \<rightleftharpoons> pCons
translations
  "[:x, xs:]" \<rightleftharpoons> "CONST pCons x [:xs:]"
  "[:x:]" \<rightleftharpoons> "CONST pCons x 0"

lemma degree_0_id: 
  assumes "degree p = 0"
  shows "[: coeff p 0 :] = p"
  by sorry

lemma degree0_coeffs: "degree p = 0 \<Longrightarrow> \<exists> a. p = [: a :]"
  by sorry

lemma degree1_coeffs:
  fixes p :: "'a::zero poly"
  assumes "degree p = 1"
  obtains a b where "p = [: b, a :]" "a \<noteq> 0"
  by sorry

lemma degree2_coeffs:
  fixes p :: "'a::zero poly"
  assumes "degree p = 2"
  obtains a b c where "p = [: c, b, a :]" "a \<noteq> 0"
  by sorry


subsection \<open>Representation of polynomials by lists of coefficients\<close>

primrec Poly :: "'a::zero list \<Rightarrow> 'a poly"
  where
    [code_post]: "Poly [] = 0"
  | [code_post]: "Poly (a # as) = pCons a (Poly as)"

lemma Poly_replicate_0 [simp]: "Poly (replicate n 0) = 0"
  by sorry

lemma Poly_eq_0: "Poly as = 0 \<longleftrightarrow> (\<exists>n. as = replicate n 0)"
  by sorry

lemma Poly_append_replicate_0 [simp]: "Poly (as @ replicate n 0) = Poly as"
  by sorry

lemma Poly_snoc_zero [simp]: "Poly (as @ [0]) = Poly as"
  by sorry

lemma Poly_cCons_eq_pCons_Poly [simp]: "Poly (a ## p) = pCons a (Poly p)"
  by sorry

lemma Poly_on_rev_starting_with_0 [simp]: "hd as = 0 \<Longrightarrow> Poly (rev (tl as)) = Poly (rev as)"
  by sorry

lemma degree_Poly: "degree (Poly xs) \<le> length xs"
  by sorry

lemma coeff_Poly_eq [simp]: "coeff (Poly xs) = nth_default 0 xs"
  by sorry

definition coeffs :: "'a poly \<Rightarrow> 'a::zero list"
  where "coeffs p = (if p = 0 then [] else map (\<lambda>i. coeff p i) [0 ..< Suc (degree p)])"

lemma coeffs_eq_Nil [simp]: "coeffs p = [] \<longleftrightarrow> p = 0"
  by sorry

lemma not_0_coeffs_not_Nil: "p \<noteq> 0 \<Longrightarrow> coeffs p \<noteq> []"
  by sorry

lemma coeffs_0_eq_Nil [simp]: "coeffs 0 = []"
  by sorry

lemma coeffs_pCons_eq_cCons [simp]: "coeffs (pCons a p) = a ## coeffs p"
  by sorry

lemma length_coeffs: "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = degree p + 1"
  by sorry

lemma coeffs_nth: "p \<noteq> 0 \<Longrightarrow> n \<le> degree p \<Longrightarrow> coeffs p ! n = coeff p n"
  by sorry

lemma coeff_in_coeffs: "p \<noteq> 0 \<Longrightarrow> n \<le> degree p \<Longrightarrow> coeff p n \<in> set (coeffs p)"
  by sorry

lemma not_0_cCons_eq [simp]: "p \<noteq> 0 \<Longrightarrow> a ## coeffs p = a # coeffs p"
  by sorry

lemma Poly_coeffs [simp, code abstype]: "Poly (coeffs p) = p"
  by sorry

lemma coeffs_Poly [simp]: "coeffs (Poly as) = strip_while (HOL.eq 0) as"
  by sorry

lemma no_trailing_coeffs [simp]:
  "no_trailing (HOL.eq 0) (coeffs p)"
  by sorry

lemma strip_while_coeffs [simp]:
  "strip_while (HOL.eq 0) (coeffs p) = coeffs p"
  by sorry

lemma coeffs_eq_iff: "p = q \<longleftrightarrow> coeffs p = coeffs q"
  (is "?P \<longleftrightarrow> ?Q")
  by sorry

lemma nth_default_coeffs_eq: "nth_default 0 (coeffs p) = coeff p"
  by sorry

lemma range_coeff: "range (coeff p) = insert 0 (set (coeffs p))" 
  by sorry

lemma [code]: "coeff p = nth_default 0 (coeffs p)"
  by sorry

lemma coeffs_eqI:
  assumes coeff: "\<And>n. coeff p n = nth_default 0 xs n"
  assumes zero: "no_trailing (HOL.eq 0) xs"
  shows "coeffs p = xs"
  by sorry

lemma degree_eq_length_coeffs [code]: "degree p = length (coeffs p) - 1"
  by sorry

lemma length_coeffs_degree: "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = Suc (degree p)"
  by sorry

lemma [code abstract]: "coeffs 0 = []"
  by sorry

lemma [code abstract]: "coeffs (pCons a p) = a ## coeffs p"
  by sorry

lemma set_coeffs_subset_singleton_0_iff [simp]:
  "set (coeffs p) \<subseteq> {0} \<longleftrightarrow> p = 0"
  by sorry

lemma set_coeffs_not_only_0 [simp]:
  "set (coeffs p) \<noteq> {0}"
  by sorry

lemma forall_coeffs_conv:
  "(\<forall>n. P (coeff p n)) \<longleftrightarrow> (\<forall>c \<in> set (coeffs p). P c)" if "P 0"
  by sorry

instantiation poly :: ("{zero, equal}") equal
begin

definition [code]: "HOL.equal (p::'a poly) q \<longleftrightarrow> HOL.equal (coeffs p) (coeffs q)"

instance
  by standard (simp add: equal equal_poly_def coeffs_eq_iff)

end

lemma [code nbe]: "HOL.equal (p :: _ poly) p \<longleftrightarrow> True"
  by sorry

definition is_zero :: "'a::zero poly \<Rightarrow> bool"
  where [code]: "is_zero p \<longleftrightarrow> List.null (coeffs p)"

lemma is_zero_null [code_abbrev]: "is_zero p \<longleftrightarrow> p = 0"
  by sorry


text \<open>Reconstructing the polynomial from the list\<close>
  \<comment> \<open>contributed by Sebastiaan J.C. Joosten and René Thiemann\<close>

definition poly_of_list :: "'a::comm_monoid_add list \<Rightarrow> 'a poly"
  where [simp]: "poly_of_list = Poly"

lemma poly_of_list_impl [code abstract]: "coeffs (poly_of_list as) = strip_while (HOL.eq 0) as"
  by sorry


subsection \<open>Fold combinator for polynomials\<close>

definition fold_coeffs :: "('a::zero \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a poly \<Rightarrow> 'b \<Rightarrow> 'b"
  where "fold_coeffs f p = foldr f (coeffs p)"

lemma fold_coeffs_0_eq [simp]: "fold_coeffs f 0 = id"
  by sorry

lemma fold_coeffs_pCons_eq [simp]: "f 0 = id \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by sorry

lemma fold_coeffs_pCons_0_0_eq [simp]: "fold_coeffs f (pCons 0 0) = id"
  by sorry

lemma fold_coeffs_pCons_coeff_not_0_eq [simp]:
  "a \<noteq> 0 \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by sorry

lemma fold_coeffs_pCons_not_0_0_eq [simp]:
  "p \<noteq> 0 \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by sorry


subsection \<open>Canonical morphism on polynomials -- evaluation\<close>

definition poly :: \<open>'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>poly p a = horner_sum id a (coeffs p)\<close>

lemma poly_eq_fold_coeffs:
  \<open>poly p = fold_coeffs (\<lambda>a f x. a + x * f x) p (\<lambda>x. 0)\<close>
  by sorry

lemma poly_0 [simp]: "poly 0 x = 0"
  by sorry

lemma poly_pCons [simp]: "poly (pCons a p) x = a + x * poly p x"
  by sorry

lemma poly_altdef: "poly p x = (\<Sum>i\<le>degree p. coeff p i * x ^ i)"
  for x :: "'a::{comm_semiring_0,semiring_1}"
  by sorry

lemma poly_as_sum:
  fixes p :: "'a::comm_semiring_1 poly"
  shows "poly p x = (\<Sum>i\<le>degree p. x ^ i * coeff p i)"
  by sorry

lemma poly_0_coeff_0: "poly p 0 = coeff p 0"
  by sorry

lemma poly_zero:
  fixes p :: "'a :: comm_ring_1 poly"
  assumes x: "poly p x = 0" shows "p = 0 \<longleftrightarrow> degree p = 0"
  by sorry


subsection \<open>Monomials\<close>

lift_definition monom :: "'a \<Rightarrow> nat \<Rightarrow> 'a::zero poly"
  is "\<lambda>a m n. if m = n then a else 0"
  by (simp add: MOST_iff_cofinite)

lemma coeff_monom [simp]: "coeff (monom a m) n = (if m = n then a else 0)"
  by sorry

lemma monom_0: "monom a 0 = [:a:]"
  by sorry

lemma monom_Suc: "monom a (Suc n) = pCons 0 (monom a n)"
  by sorry

lemma monom_eq_0 [simp]: "monom 0 n = 0"
  by sorry

lemma monom_eq_0_iff [simp]: "monom a n = 0 \<longleftrightarrow> a = 0"
  by sorry

lemma monom_eq_iff [simp]: "monom a n = monom b n \<longleftrightarrow> a = b"
  by sorry

lemma degree_monom_le: "degree (monom a n) \<le> n"
  by sorry

lemma degree_monom_eq: "a \<noteq> 0 \<Longrightarrow> degree (monom a n) = n"
  by sorry

lemma coeffs_monom [code abstract]:
  "coeffs (monom a n) = (if a = 0 then [] else replicate n 0 @ [a])"
  by sorry

lemma fold_coeffs_monom [simp]: "a \<noteq> 0 \<Longrightarrow> fold_coeffs f (monom a n) = f 0 ^^ n \<circ> f a"
  by sorry

lemma poly_monom: "poly (monom a n) x = a * x ^ n"
  for a x :: "'a::comm_semiring_1"
  by sorry

lemma monom_eq_iff': "monom c n = monom d m \<longleftrightarrow>  c = d \<and> (c = 0 \<or> n = m)"
  by sorry

lemma monom_eq_const_iff: "monom c n = [:d:] \<longleftrightarrow> c = d \<and> (c = 0 \<or> n = 0)"
  by sorry


subsection \<open>Leading coefficient\<close>

abbreviation lead_coeff:: "'a::zero poly \<Rightarrow> 'a"
  where "lead_coeff p \<equiv> coeff p (degree p)"

lemma lead_coeff_pCons[simp]:
  "p \<noteq> 0 \<Longrightarrow> lead_coeff (pCons a p) = lead_coeff p"
  "p = 0 \<Longrightarrow> lead_coeff (pCons a p) = a"
  by sorry

lemma lead_coeff_monom [simp]: "lead_coeff (monom c n) = c"
  by sorry

lemma last_coeffs_eq_coeff_degree:
  "last (coeffs p) = lead_coeff p" if "p \<noteq> 0"
  by sorry

lemma lead_coeff_list_def:
  "lead_coeff p = (if coeffs p=[] then 0 else last (coeffs p))"
  by sorry

subsection \<open>Addition and subtraction\<close>

instantiation poly :: (comm_monoid_add) comm_monoid_add
begin

lift_definition plus_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p q n. coeff p n + coeff q n"
proof -
  fix q p :: "'a poly"
  show "\<forall>\<^sub>\<infinity>n. coeff p n + coeff q n = 0"
    using MOST_coeff_eq_0[of p] MOST_coeff_eq_0[of q] by eventually_elim simp
qed

lemma coeff_add [simp]: "coeff (p + q) n = coeff p n + coeff q n"
  by sorry

instance
proof
  fix p q r :: "'a poly"
  show "(p + q) + r = p + (q + r)"
    by (simp add: poly_eq_iff add.assoc)
  show "p + q = q + p"
    by (simp add: poly_eq_iff add.commute)
  show "0 + p = p"
    by (simp add: poly_eq_iff)
qed

end

instantiation poly :: (cancel_comm_monoid_add) cancel_comm_monoid_add
begin

lift_definition minus_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p q n. coeff p n - coeff q n"
proof -
  fix q p :: "'a poly"
  show "\<forall>\<^sub>\<infinity>n. coeff p n - coeff q n = 0"
    using MOST_coeff_eq_0[of p] MOST_coeff_eq_0[of q] by eventually_elim simp
qed

lemma coeff_diff [simp]: "coeff (p - q) n = coeff p n - coeff q n"
  by sorry

instance
proof
  fix p q r :: "'a poly"
  show "p + q - p = q"
    by (simp add: poly_eq_iff)
  show "p - q - r = p - (q + r)"
    by (simp add: poly_eq_iff diff_diff_eq)
qed

end

instantiation poly :: (ab_group_add) ab_group_add
begin

lift_definition uminus_poly :: "'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p n. - coeff p n"
proof -
  fix p :: "'a poly"
  show "\<forall>\<^sub>\<infinity>n. - coeff p n = 0"
    using MOST_coeff_eq_0 by simp
qed

lemma coeff_minus [simp]: "coeff (- p) n = - coeff p n"
  by sorry

instance
proof
  fix p q :: "'a poly"
  show "- p + p = 0"
    by (simp add: poly_eq_iff)
  show "p - q = p + - q"
    by (simp add: poly_eq_iff)
qed

end

lemma add_pCons [simp]: "pCons a p + pCons b q = pCons (a + b) (p + q)"
  by sorry

lemma minus_pCons [simp]: "- pCons a p = pCons (- a) (- p)"
  by sorry

lemma diff_pCons [simp]: "pCons a p - pCons b q = pCons (a - b) (p - q)"
  by sorry

lemma degree_add_le_max: "degree (p + q) \<le> max (degree p) (degree q)"
  by sorry

lemma degree_add_le: "degree p \<le> n \<Longrightarrow> degree q \<le> n \<Longrightarrow> degree (p + q) \<le> n"
  by sorry

lemma degree_add_less: "degree p < n \<Longrightarrow> degree q < n \<Longrightarrow> degree (p + q) < n"
  by sorry

lemma degree_add_eq_right: assumes "degree p < degree q" shows "degree (p + q) = degree q"
  by sorry

lemma degree_add_eq_left: "degree q < degree p \<Longrightarrow> degree (p + q) = degree p"
  by sorry

lemma degree_minus [simp]: "degree (- p) = degree p"
  by sorry

lemma lead_coeff_add_le: "degree p < degree q \<Longrightarrow> lead_coeff (p + q) = lead_coeff q"
  by sorry

lemma lead_coeff_minus: "lead_coeff (- p) = - lead_coeff p"
  by sorry

lemma degree_diff_le_max: "degree (p - q) \<le> max (degree p) (degree q)"
  for p q :: "'a::ab_group_add poly"
  by sorry

lemma degree_diff_le: "degree p \<le> n \<Longrightarrow> degree q \<le> n \<Longrightarrow> degree (p - q) \<le> n"
  for p q :: "'a::ab_group_add poly"
  by sorry

lemma degree_diff_less: "degree p < n \<Longrightarrow> degree q < n \<Longrightarrow> degree (p - q) < n"
  for p q :: "'a::ab_group_add poly"
  by sorry

lemma add_monom: "monom a n + monom b n = monom (a + b) n"
  by sorry

lemma diff_monom: "monom a n - monom b n = monom (a - b) n"
  by sorry

lemma minus_monom: "- monom a n = monom (- a) n"
  by sorry

lemma coeff_sum: "coeff (\<Sum>x\<in>A. p x) i = (\<Sum>x\<in>A. coeff (p x) i)"
  by sorry

lemma monom_sum: "monom (\<Sum>x\<in>A. a x) n = (\<Sum>x\<in>A. monom (a x) n)"
  by sorry

fun plus_coeffs :: "'a::comm_monoid_add list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "plus_coeffs xs [] = xs"
  | "plus_coeffs [] ys = ys"
  | "plus_coeffs (x # xs) (y # ys) = (x + y) ## plus_coeffs xs ys"

lemma coeffs_plus_eq_plus_coeffs [code abstract]:
  "coeffs (p + q) = plus_coeffs (coeffs p) (coeffs q)"
  by sorry

lemma coeffs_uminus [code abstract]:
  "coeffs (- p) = map uminus (coeffs p)"
  by sorry

lemma [code]: "p - q = p + - q"
  for p q :: "'a::ab_group_add poly"
  by sorry

lemma poly_add [simp]: "poly (p + q) x = poly p x + poly q x"
  by sorry

lemma poly_minus [simp]: "poly (- p) x = - poly p x"
  for x :: "'a::comm_ring"
  by sorry

lemma poly_diff [simp]: "poly (p - q) x = poly p x - poly q x"
  for x :: "'a::comm_ring"
  by sorry

lemma poly_sum: "poly (\<Sum>k\<in>A. p k) x = (\<Sum>k\<in>A. poly (p k) x)"
  by sorry

lemma poly_sum_list: "poly (\<Sum>p\<leftarrow>ps. p) y = (\<Sum>p\<leftarrow>ps. poly p y)"
  by sorry

lemma poly_sum_mset: "poly (\<Sum>x\<in>#A. p x) y = (\<Sum>x\<in>#A. poly (p x) y)"
  by sorry

lemma degree_sum_le: "finite S \<Longrightarrow> (\<And>p. p \<in> S \<Longrightarrow> degree (f p) \<le> n) \<Longrightarrow> degree (sum f S) \<le> n"
  by sorry

lemma degree_sum_less:
  assumes "\<And>x. x \<in> A \<Longrightarrow> degree (f x) < n" "n > 0"
  shows   "degree (sum f A) < n"
  by sorry

lemma poly_as_sum_of_monoms':
  assumes "degree p \<le> n"
  shows "(\<Sum>i\<le>n. monom (coeff p i) i) = p"
  by sorry

lemma poly_as_sum_of_monoms: "(\<Sum>i\<le>degree p. monom (coeff p i) i) = p"
  by sorry

lemma Poly_snoc: "Poly (xs @ [x]) = Poly xs + monom x (length xs)"
  by sorry


subsection \<open>Multiplication by a constant, polynomial multiplication and the unit polynomial\<close>

lift_definition smult :: "'a::comm_semiring_0 \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p n. a * coeff p n"
proof -
  fix a :: 'a and p :: "'a poly"
  show "\<forall>\<^sub>\<infinity> i. a * coeff p i = 0"
    using MOST_coeff_eq_0[of p] by eventually_elim simp
qed

lemma coeff_smult [simp]: "coeff (smult a p) n = a * coeff p n"
  by sorry

lemma degree_smult_le: "degree (smult a p) \<le> degree p"
  by sorry

lemma smult_smult [simp]: "smult a (smult b p) = smult (a * b) p"
  by sorry

lemma smult_0_right [simp]: "smult a 0 = 0"
  by sorry

lemma smult_0_left [simp]: "smult 0 p = 0"
  by sorry

lemma smult_1_left [simp]: "smult (1::'a::comm_semiring_1) p = p"
  by sorry

lemma smult_add_right: "smult a (p + q) = smult a p + smult a q"
  by sorry

lemma smult_add_left: "smult (a + b) p = smult a p + smult b p"
  by sorry

lemma smult_minus_right [simp]: "smult a (- p) = - smult a p"
  for a :: "'a::comm_ring"
  by sorry

lemma smult_minus_left [simp]: "smult (- a) p = - smult a p"
  for a :: "'a::comm_ring"
  by sorry

lemma smult_diff_right: "smult a (p - q) = smult a p - smult a q"
  for a :: "'a::comm_ring"
  by sorry

lemma smult_diff_left: "smult (a - b) p = smult a p - smult b p"
  for a b :: "'a::comm_ring"
  by sorry

lemmas smult_distribs =
  smult_add_left smult_add_right
  smult_diff_left smult_diff_right

lemma smult_pCons [simp]: "smult a (pCons b p) = pCons (a * b) (smult a p)"
  by sorry

lemma smult_monom: "smult a (monom b n) = monom (a * b) n"
  by sorry

lemma smult_Poly: "smult c (Poly xs) = Poly (map ((*) c) xs)"
  by sorry

lemma degree_smult_eq [simp]: "degree (smult a p) = (if a = 0 then 0 else degree p)"
  for a :: "'a::{comm_semiring_0,semiring_no_zero_divisors}"
  by sorry

lemma smult_eq_0_iff [simp]: "smult a p = 0 \<longleftrightarrow> a = 0 \<or> p = 0"
  for a :: "'a::{comm_semiring_0,semiring_no_zero_divisors}"
  by sorry

lemma coeffs_smult [code abstract]:
  "coeffs (smult a p) = (if a = 0 then [] else map (Groups.times a) (coeffs p))"
  for p :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma smult_eq_iff:
  fixes b :: "'a :: field"
  assumes "b \<noteq> 0"
  shows "smult a p = smult b q \<longleftrightarrow> smult (a / b) p = q"
    (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma smult_cancel:
  fixes p::"'a::idom poly"
  assumes "c\<noteq>0" and smult: "smult c p = smult c q" 
  shows "p=q" 
  by sorry
  
instantiation poly :: (comm_semiring_0) comm_semiring_0
begin

definition "p * q = fold_coeffs (\<lambda>a p. smult a q + pCons 0 p) p 0"

lemma mult_poly_0_left: "(0::'a poly) * q = 0"
  by sorry

lemma mult_pCons_left [simp]: "pCons a p * q = smult a q + pCons 0 (p * q)"
  by sorry

lemma mult_poly_0_right: "p * (0::'a poly) = 0"
  by sorry

lemma mult_pCons_right [simp]: "p * pCons a q = smult a p + pCons 0 (p * q)"
  by sorry

lemmas mult_poly_0 = mult_poly_0_left mult_poly_0_right

lemma mult_smult_left [simp]: "smult a p * q = smult a (p * q)"
  by sorry

lemma mult_smult_right [simp]: "p * smult a q = smult a (p * q)"
  by sorry

lemma mult_poly_add_left: "(p + q) * r = p * r + q * r"
  for p q r :: "'a poly"
  by sorry

instance
proof
  fix p q r :: "'a poly"
  show 0: "0 * p = 0"
    by (rule mult_poly_0_left)
  show "p * 0 = 0"
    by (rule mult_poly_0_right)
  show "(p + q) * r = p * r + q * r"
    by (rule mult_poly_add_left)
  show "(p * q) * r = p * (q * r)"
    by (induct p) (simp_all add: mult_poly_0 mult_poly_add_left)
  show "p * q = q * p"
    by (induct p) (simp_all add: mult_poly_0)
qed

end

lemma coeff_mult_degree_sum:
  "coeff (p * q) (degree p + degree q) = coeff p (degree p) * coeff q (degree q)"
  by sorry

instance poly :: ("{comm_semiring_0,semiring_no_zero_divisors}") semiring_no_zero_divisors
proof
  fix p q :: "'a poly"
  assume "p \<noteq> 0" and "q \<noteq> 0"
  have "coeff (p * q) (degree p + degree q) = coeff p (degree p) * coeff q (degree q)"
    by (rule coeff_mult_degree_sum)
  also from \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> have "coeff p (degree p) * coeff q (degree q) \<noteq> 0"
    by simp
  finally have "\<exists>n. coeff (p * q) n \<noteq> 0" ..
  then show "p * q \<noteq> 0"
    by (simp add: poly_eq_iff)
qed

instance poly :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

lemma coeff_mult: "coeff (p * q) n = (\<Sum>i\<le>n. coeff p i * coeff q (n-i))"
  by sorry

lemma coeff_mult_0: "coeff (p * q) 0 = coeff p 0 * coeff q 0"
  by sorry

lemma degree_mult_le: "degree (p * q) \<le> degree p + degree q"
  by sorry

lemma mult_monom: "monom a m * monom b n = monom (a * b) (m + n)"
  by sorry

instantiation poly :: (comm_semiring_1) comm_semiring_1
begin

lift_definition one_poly :: "'a poly"
  is "\<lambda>n. of_bool (n = 0)"
  by (rule MOST_SucD) simp

lemma coeff_1 [simp]:
  "coeff 1 n = of_bool (n = 0)"
  by sorry

lemma one_pCons:
  "1 = [:1:]"
  by sorry

lemma pCons_one:
  "[:1:] = 1"
  by sorry

instance
  by standard (simp_all add: one_pCons)

end

lemma poly_1 [simp]:
  "poly 1 x = 1"
  by sorry

lemma one_poly_eq_simps [simp]:
  "1 = [:1:] \<longleftrightarrow> True"
  "[:1:] = 1 \<longleftrightarrow> True"
  by sorry

lemma degree_1 [simp]:
  "degree 1 = 0"
  by sorry

lemma coeffs_1_eq [simp, code abstract]:
  "coeffs 1 = [1]"
  by sorry

lemma smult_one [simp]:
  "smult c 1 = [:c:]"
  by sorry

lemma smult_sum: "smult (\<Sum>i \<in> S. f i) p = (\<Sum>i \<in> S. smult (f i) p)"
  by sorry

lemma smult_power: "(smult a p) ^ n = smult (a ^ n) (p ^ n)"
  by sorry

lemma monom_eq_1 [simp]:
  "monom 1 0 = 1"
  by sorry

lemma monom_eq_1_iff:
  "monom c n = 1 \<longleftrightarrow> c = 1 \<and> n = 0"
  by sorry

lemma monom_altdef:
  "monom c n = smult c ([:0, 1:] ^ n)"
  by sorry

lemma degree_sum_list_le: "(\<And> p . p \<in> set ps \<Longrightarrow> degree p \<le> n)
  \<Longrightarrow> degree (sum_list ps) \<le> n"
  by sorry

lemma degree_prod_list_le: "degree (prod_list ps) \<le> sum_list (map degree ps)"
  by sorry

instance poly :: ("{comm_semiring_1,semiring_1_no_zero_divisors}") semiring_1_no_zero_divisors ..
instance poly :: (comm_ring) comm_ring ..
instance poly :: (comm_ring_1) comm_ring_1 ..
instance poly :: (comm_ring_1) comm_semiring_1_cancel ..

lemma prod_smult: "(\<Prod>x\<in>A. smult (c x) (p x)) = smult (prod c A) (prod p A)"
  by sorry

lemma degree_power_le: "degree (p ^ n) \<le> degree p * n"
  by sorry

lemma coeff_0_power: "coeff (p ^ n) 0 = coeff p 0 ^ n"
  by sorry

lemma poly_smult [simp]: "poly (smult a p) x = a * poly p x"
  by sorry

lemma poly_mult [simp]: "poly (p * q) x = poly p x * poly q x"
  by sorry

lemma poly_power [simp]: "poly (p ^ n) x = poly p x ^ n"
  for p :: "'a::comm_semiring_1 poly"
  by sorry

lemma poly_prod: "poly (\<Prod>k\<in>A. p k) x = (\<Prod>k\<in>A. poly (p k) x)"
  by sorry

lemma poly_prod_list: "poly (\<Prod>p\<leftarrow>ps. p) y = (\<Prod>p\<leftarrow>ps. poly p y)"
  by sorry

lemma poly_prod_mset: "poly (\<Prod>x\<in>#A. p x) y = (\<Prod>x\<in>#A. poly (p x) y)"
  by sorry

lemma poly_const_pow: "[: c :] ^ n = [: c ^ n :]"
  by sorry

lemma monom_power: "monom c n ^ k = monom (c ^ k) (n * k)"
  by sorry

lemma degree_prod_sum_le: "finite S \<Longrightarrow> degree (prod f S) \<le> sum (degree \<circ> f) S"
  by sorry

lemma coeff_0_prod_list: "coeff (prod_list xs) 0 = prod_list (map (\<lambda>p. coeff p 0) xs)"
  by sorry

lemma coeff_monom_mult: "coeff (monom c n * p) k = (if k < n then 0 else c * coeff p (k - n))"
  by sorry

lemma coeff_monom_Suc: "coeff (monom a (Suc d) * p) (Suc i) = coeff (monom a d * p) i"
  by sorry

lemma monom_1_dvd_iff': "monom 1 n dvd p \<longleftrightarrow> (\<forall>k<n. coeff p k = 0)"
  by sorry

lemma coeff_sum_monom:
  assumes n: "n \<le> d"
  shows "coeff (\<Sum>i\<le>d. monom (f i) i) n = f n" (is "?l = _")
  by sorry

subsection \<open>Mapping polynomials\<close>

definition map_poly :: "('a :: zero \<Rightarrow> 'b :: zero) \<Rightarrow> 'a poly \<Rightarrow> 'b poly"
  where "map_poly f p = Poly (map f (coeffs p))"

lemma map_poly_0 [simp]: "map_poly f 0 = 0"
  by sorry

lemma map_poly_1: "map_poly f 1 = [:f 1:]"
  by sorry

lemma map_poly_1' [simp]: "f 1 = 1 \<Longrightarrow> map_poly f 1 = 1"
  by sorry

lemma coeff_map_poly:
  assumes "f 0 = 0"
  shows "coeff (map_poly f p) n = f (coeff p n)"
  by sorry

lemma lead_coeff_map_poly_nz:
  assumes "f (lead_coeff p) \<noteq> 0" "f 0 = 0"
  shows "lead_coeff (map_poly f p) = f (lead_coeff p)"
  by sorry
        
lemma coeffs_map_poly [code abstract]:
  "coeffs (map_poly f p) = strip_while ((=) 0) (map f (coeffs p))"
  by sorry

lemma coeffs_map_poly':
  assumes "\<And>x. x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "coeffs (map_poly f p) = map f (coeffs p)"
  by sorry

lemma set_coeffs_map_poly:
  "(\<And>x. f x = 0 \<longleftrightarrow> x = 0) \<Longrightarrow> set (coeffs (map_poly f p)) = f ` set (coeffs p)"
  by sorry

lemma degree_map_poly:
  assumes "\<And>x. x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "degree (map_poly f p) = degree p"
  by sorry

lemma map_poly_eq_0_iff:
  assumes "f 0 = 0" "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "map_poly f p = 0 \<longleftrightarrow> p = 0"
  by sorry

lemma map_poly_smult:
  assumes "f 0 = 0""\<And>c x. f (c * x) = f c * f x"
  shows "map_poly f (smult c p) = smult (f c) (map_poly f p)"
  by sorry

lemma map_poly_pCons:
  assumes "f 0 = 0"
  shows "map_poly f (pCons c p) = pCons (f c) (map_poly f p)"
  by sorry

lemma map_poly_map_poly:
  assumes "f 0 = 0" "g 0 = 0"
  shows "map_poly f (map_poly g p) = map_poly (f \<circ> g) p"
  by sorry

lemma map_poly_id [simp]: "map_poly id p = p"
  by sorry

lemma map_poly_id' [simp]: "map_poly (\<lambda>x. x) p = p"
  by sorry

lemma map_poly_cong:
  assumes "(\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = g x)"
  shows "map_poly f p = map_poly g p"
  by sorry

lemma map_poly_monom: "f 0 = 0 \<Longrightarrow> map_poly f (monom c n) = monom (f c) n"
  by sorry

lemma map_poly_idI:
  assumes "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = x"
  shows "map_poly f p = p"
  by sorry

lemma map_poly_idI':
  assumes "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = x"
  shows "p = map_poly f p"
  by sorry

lemma smult_conv_map_poly: "smult c p = map_poly (\<lambda>x. c * x) p"
  by sorry

lemma poly_cnj: "cnj (poly p z) = poly (map_poly cnj p) (cnj z)"
  by sorry

lemma monom_pCons_0_monom:
  "monom (pCons 0 (monom a n)) d = map_poly (pCons 0) (monom (monom a n) d)"
  by sorry

lemma pCons_0_add: "pCons 0 (p + q) = pCons 0 p + pCons 0 q" 
  by sorry

lemma sum_pCons_0_commute:
  "sum (\<lambda>i. pCons 0 (f i)) S = pCons 0 (sum f S)"
  by sorry

lemma pCons_0_as_mult:
  fixes p:: "'a :: comm_semiring_1 poly"
  shows "pCons 0 p = [:0,1:] * p" 
  by sorry

lemma poly_cnj_real:
  assumes "\<And>n. poly.coeff p n \<in> \<real>"
  shows   "cnj (poly p z) = poly p (cnj z)"
  by sorry

lemma real_poly_cnj_root_iff:
  assumes "\<And>n. poly.coeff p n \<in> \<real>"
  shows   "poly p (cnj z) = 0 \<longleftrightarrow> poly p z = 0"
  by sorry

lemma sum_to_poly: "(\<Sum>x\<in>A. [:f x:]) = [:\<Sum>x\<in>A. f x:]"
  by sorry

lemma diff_to_poly: "[:c:] - [:d:] = [:c - d:]"
  by sorry

lemma mult_to_poly: "[:c:] * [:d:] = [:c * d:]"
  by sorry

lemma prod_to_poly: "(\<Prod>x\<in>A. [:f x:]) = [:\<Prod>x\<in>A. f x:]"
  by sorry

lemma poly_map_poly_cnj [simp]: "poly (map_poly cnj p) x = cnj (poly p (cnj x))"
  by sorry

lemma map_poly_degree_eq:
  assumes "f (lead_coeff p) \<noteq> 0"
  shows "degree (map_poly f p) = degree p"  
  by sorry
  
lemma map_poly_degree_less:
  assumes "f (lead_coeff p) =0" "degree p\<noteq>0"
  shows "degree (map_poly f p) < degree p" 
  by sorry
  
lemma map_poly_degree_leq:
  shows "degree (map_poly f p) \<le> degree p"
  by sorry

subsection \<open>Conversions\<close>

lemma of_nat_poly: "of_nat n = [:of_nat n:]"
  by sorry

lemma of_nat_monom: "of_nat n = monom (of_nat n) 0"
  by sorry

lemma degree_of_nat [simp]: "degree (of_nat n) = 0"
  by sorry

lemma lead_coeff_of_nat [simp]: "lead_coeff (of_nat n) = of_nat n"
  by sorry

lemma of_int_poly: "of_int k = [:of_int k:]"
  by sorry

lemma of_int_monom: "of_int k = monom (of_int k) 0"
  by sorry

lemma degree_of_int [simp]: "degree (of_int k) = 0"
  by sorry

lemma lead_coeff_of_int [simp]: "lead_coeff (of_int k) = of_int k"
  by sorry

lemma poly_of_nat [simp]: "poly (of_nat n) x = of_nat n"
  by sorry

lemma poly_of_int [simp]: "poly (of_int n) x = of_int n"
  by sorry

lemma poly_numeral [simp]: "poly (numeral n) x = numeral n"
  by sorry

lemma numeral_poly: "numeral n = [:numeral n:]"
  by sorry

lemma numeral_monom:
  "numeral n = monom (numeral n) 0"
  by sorry

lemma degree_numeral [simp]:
  "degree (numeral n) = 0"
  by sorry

lemma lead_coeff_numeral [simp]:
  "lead_coeff (numeral n) = numeral n"
  by sorry

lemma coeff_linear_poly_power:
  fixes c :: "'a :: semiring_1"
  assumes "i \<le> n"
  shows   "coeff ([:a, b:] ^ n) i = of_nat (n choose i) * b ^ i * a ^ (n - i)"
  by sorry



subsection \<open>Lemmas about divisibility\<close>

lemma dvd_smult:
  assumes "p dvd q"
  shows "p dvd smult a q"
  by sorry

lemma dvd_smult_cancel: "p dvd smult a q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> p dvd q"
  for a :: "'a::field"
  by sorry

lemma dvd_smult_iff: "a \<noteq> 0 \<Longrightarrow> p dvd smult a q \<longleftrightarrow> p dvd q"
  for a :: "'a::field"
  by sorry

lemma smult_dvd_cancel:
  assumes "smult a p dvd q"
  shows "p dvd q"
  by sorry

lemma smult_dvd: "p dvd q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> smult a p dvd q"
  for a :: "'a::field"
  by sorry

lemma smult_dvd_iff: "smult a p dvd q \<longleftrightarrow> (if a = 0 then q = 0 else p dvd q)"
  for a :: "'a::field"
  by sorry

lemma is_unit_smult_iff: "smult c p dvd 1 \<longleftrightarrow> c dvd 1 \<and> p dvd 1"
  by sorry


subsection \<open>Polynomials form an integral domain\<close>

instance poly :: (idom) idom ..

instance poly :: ("{ring_char_0, comm_ring_1}") ring_char_0
  by standard (auto simp add: of_nat_poly intro: injI)

lemma semiring_char_poly [simp]: "CHAR('a :: comm_semiring_1 poly) = CHAR('a)"
  by sorry

instance poly :: ("{semiring_prime_char,comm_semiring_1}") semiring_prime_char
  by (rule semiring_prime_charI) auto
instance poly :: ("{comm_semiring_prime_char,comm_semiring_1}") comm_semiring_prime_char
  by standard
instance poly :: ("{comm_ring_prime_char,comm_semiring_1}") comm_ring_prime_char
  by standard
instance poly :: ("{idom_prime_char,comm_semiring_1}") idom_prime_char
  by standard

lemma linear_poly_root: 
  "(a :: 'a :: comm_ring_1) \<in> set as \<Longrightarrow> poly (\<Prod> a \<leftarrow> as. [: - a, 1:]) a = 0"
  by sorry

lemma poly_sum_list_eq: "poly (sum_list ps) x = sum_list (map (\<lambda> p. poly p x) ps)"
  by sorry

lemma poly_prod_list_eq: "poly (prod_list ps) x = prod_list (map (\<lambda> p. poly p x) ps)"
  by sorry

lemma sum_list_neutral: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list xs = 0"
  by sorry

lemma prod_list_neutral: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 1) \<Longrightarrow> prod_list xs = 1"
  by sorry

lemma (in comm_monoid_mult) prod_list_map_remove1:
  "x \<in> set xs \<Longrightarrow> prod_list (map f xs) = f x * prod_list (map f (remove1 x xs))"
  by sorry

lemma poly_prod_0: "finite ps \<Longrightarrow> poly (prod f ps) x = (0 :: 'a :: field) \<longleftrightarrow> (\<exists> p \<in> ps. poly (f p) x = 0)"
  by sorry

lemma degree_mult_eq: "p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> degree (p * q) = degree p + degree q"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma degree_prod_sum_eq:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow>
     degree (prod f A :: 'a :: idom poly) = (\<Sum>x\<in>A. degree (f x))"
  by sorry

lemma dvd_imp_degree:
  \<open>degree x \<le> degree y\<close> if \<open>x dvd y\<close> \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
    for x y :: \<open>'a::{comm_semiring_1,semiring_no_zero_divisors} poly\<close>
  by sorry

lemma degree_prod_eq_sum_degree:
  fixes A :: "'a set"
  and f :: "'a \<Rightarrow> 'b::idom poly"
  assumes f0: "\<forall>i\<in>A. f i \<noteq> 0"
  shows "degree (\<Prod>i\<in>A. (f i)) = (\<Sum>i\<in>A. degree (f i))"
  by sorry

lemma degree_mult_eq_0:
  "degree (p * q) = 0 \<longleftrightarrow> p = 0 \<or> q = 0 \<or> (p \<noteq> 0 \<and> q \<noteq> 0 \<and> degree p = 0 \<and> degree q = 0)"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma degree_power_eq: "p \<noteq> 0 \<Longrightarrow> degree ((p :: 'a :: idom poly) ^ n) = n * degree p"
  by sorry

lemma degree_mult_right_le:
  fixes p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  assumes "q \<noteq> 0"
  shows "degree p \<le> degree (p * q)"
  by sorry

lemma coeff_degree_mult: "coeff (p * q) (degree (p * q)) = coeff q (degree q) * coeff p (degree p)"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma dvd_imp_degree_le: "p dvd q \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> degree p \<le> degree q"
  for p q :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  by sorry

lemma divides_degree:
  fixes p q :: "'a ::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "p dvd q"
  shows "degree p \<le> degree q \<or> q = 0"
  by sorry

lemma const_poly_dvd_iff:
  fixes c :: "'a::{comm_semiring_1,semiring_no_zero_divisors}"
  shows "[:c:] dvd p \<longleftrightarrow> (\<forall>n. c dvd coeff p n)"
  by sorry

lemma const_poly_dvd_const_poly_iff [simp]: "[:a:] dvd [:b:] \<longleftrightarrow> a dvd b"
  for a b :: "'a::{comm_semiring_1,semiring_no_zero_divisors}"
  by sorry

lemma lead_coeff_mult: "lead_coeff (p * q) = lead_coeff p * lead_coeff q"
  for p q :: "'a::{comm_semiring_0, semiring_no_zero_divisors} poly"
  by sorry

lemma lead_coeff_prod: "lead_coeff (prod f A) = (\<Prod>x\<in>A. lead_coeff (f x))"
  for f :: "'a \<Rightarrow> 'b::{comm_semiring_1, semiring_no_zero_divisors} poly"
  by sorry

lemma lead_coeff_smult: "lead_coeff (smult c p) = c * lead_coeff p"
  for p :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma lead_coeff_1 [simp]: "lead_coeff 1 = 1"
  by sorry

lemma lead_coeff_power: "lead_coeff (p ^ n) = lead_coeff p ^ n"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  by sorry


subsection \<open>Polynomials form an ordered integral domain\<close>

definition pos_poly :: "'a::linordered_semidom poly \<Rightarrow> bool"
  where "pos_poly p \<longleftrightarrow> 0 < coeff p (degree p)"

lemma pos_poly_pCons: "pos_poly (pCons a p) \<longleftrightarrow> pos_poly p \<or> (p = 0 \<and> 0 < a)"
  by sorry

lemma not_pos_poly_0 [simp]: "\<not> pos_poly 0"
  by sorry

lemma pos_poly_add: "pos_poly p \<Longrightarrow> pos_poly q \<Longrightarrow> pos_poly (p + q)"
  by sorry

lemma pos_poly_mult: "pos_poly p \<Longrightarrow> pos_poly q \<Longrightarrow> pos_poly (p * q)"
  by sorry

lemma pos_poly_total: "p = 0 \<or> pos_poly p \<or> pos_poly (- p)"
  for p :: "'a::linordered_idom poly"
  by sorry

lemma pos_poly_coeffs [code]: "pos_poly p \<longleftrightarrow> (let as = coeffs p in as \<noteq> [] \<and> last as > 0)"
  (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

instantiation poly :: (linordered_idom) linordered_idom
begin

definition "x < y \<longleftrightarrow> pos_poly (y - x)"

definition "x \<le> y \<longleftrightarrow> x = y \<or> pos_poly (y - x)"

definition "\<bar>x::'a poly\<bar> = (if x < 0 then - x else x)"

definition "sgn (x::'a poly) = (if x = 0 then 0 else if 0 < x then 1 else - 1)"

instance
proof
  fix x y z :: "'a poly"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    unfolding less_eq_poly_def less_poly_def
    using pos_poly_add by force
  then show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    using less_eq_poly_def less_poly_def by force
  show "x \<le> x"
    by (simp add: less_eq_poly_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using less_eq_poly_def pos_poly_add by fastforce
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y"
    by (simp add: less_eq_poly_def)
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_poly_def
    using pos_poly_total [of "x - y"]
    by auto
  show "x < y \<Longrightarrow> 0 < z \<Longrightarrow> z * x < z * y"
    by (simp add: less_poly_def right_diff_distrib [symmetric] pos_poly_mult)
  show "\<bar>x\<bar> = (if x < 0 then - x else x)"
    by (rule abs_poly_def)
  show "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)"
    by (rule sgn_poly_def)
qed

end

text \<open>TODO: Simplification rules for comparisons\<close>


subsection \<open>Synthetic division and polynomial roots\<close>

subsubsection \<open>Synthetic division\<close>

text \<open>Synthetic division is simply division by the linear polynomial \<^term>\<open>x - c\<close>.\<close>

definition synthetic_divmod :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly \<times> 'a"
  where "synthetic_divmod p c = fold_coeffs (\<lambda>a (q, r). (pCons r q, a + c * r)) p (0, 0)"

definition synthetic_div :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly"
  where "synthetic_div p c = fst (synthetic_divmod p c)"

lemma synthetic_divmod_0 [simp]: "synthetic_divmod 0 c = (0, 0)"
  by sorry

lemma synthetic_divmod_pCons [simp]:
  "synthetic_divmod (pCons a p) c = (\<lambda>(q, r). (pCons r q, a + c * r)) (synthetic_divmod p c)"
  by sorry

lemma synthetic_div_0 [simp]: "synthetic_div 0 c = 0"
  by sorry

lemma synthetic_div_unique_lemma: "smult c p = pCons a p \<Longrightarrow> p = 0"
  by sorry

lemma snd_synthetic_divmod: "snd (synthetic_divmod p c) = poly p c"
  by sorry

lemma synthetic_div_pCons [simp]:
  "synthetic_div (pCons a p) c = pCons (poly p c) (synthetic_div p c)"
  by sorry

lemma synthetic_div_eq_0_iff: "synthetic_div p c = 0 \<longleftrightarrow> degree p = 0"
  by sorry

lemma degree_synthetic_div: "degree (synthetic_div p c) = degree p - 1"
  by sorry

lemma synthetic_div_correct:
  "p + smult c (synthetic_div p c) = pCons (poly p c) (synthetic_div p c)"
  by sorry

lemma synthetic_div_unique: "p + smult c q = pCons r q \<Longrightarrow> r = poly p c \<and> q = synthetic_div p c"
  by sorry

lemma synthetic_div_correct': "[:-c, 1:] * synthetic_div p c + [:poly p c:] = p"
  for c :: "'a::comm_ring_1"
  by sorry


subsubsection \<open>Polynomial roots\<close>

lemma poly_eq_0_iff_dvd: "poly p c = 0 \<longleftrightarrow> [:- c, 1:] dvd p"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for c :: "'a::comm_ring_1"
  by sorry

lemma dvd_iff_poly_eq_0: "[:c, 1:] dvd p \<longleftrightarrow> poly p (- c) = 0"
  for c :: "'a::comm_ring_1"
  by sorry

lemma poly_roots_finite: "p \<noteq> 0 \<Longrightarrow> finite {x. poly p x = 0}"
  for p :: "'a::{comm_ring_1,ring_no_zero_divisors} poly"
  by sorry

lemma poly_eq_poly_eq_iff: "poly p = poly q \<longleftrightarrow> p = q"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for p q :: "'a::{comm_ring_1,ring_no_zero_divisors,ring_char_0} poly"
  by sorry

text \<open>A nice extension rule for polynomials.\<close>
lemma poly_ext:
  fixes p q :: "'a :: {ring_char_0, idom} poly"
  assumes "\<And>x. poly p x = poly q x" shows "p = q"
  by sorry

text \<open>Copied from non-negative variants.\<close>
lemma coeff_linear_power_neg[simp]:
  fixes a :: "'a::comm_ring_1"
  shows "coeff ([:a, -1:] ^ n) n = (-1)^n"
  by sorry

lemma degree_linear_power_neg[simp]:
  fixes a :: "'a::{idom,comm_ring_1}"
  shows "degree ([:a, -1:] ^ n) = n"
  by sorry

lemma poly_all_0_iff_0: "(\<forall>x. poly p x = 0) \<longleftrightarrow> p = 0"
  for p :: "'a::{ring_char_0,comm_ring_1,ring_no_zero_divisors} poly"
  by sorry

lemma poly_roots_degree:
  fixes p :: "'a::{comm_ring_1,ring_no_zero_divisors} poly"
  assumes "p \<noteq> 0"
  shows   "card {x. poly p x = 0} \<le> degree p"
  by sorry

lemma poly_eqI_degree:
  fixes p q :: "'a :: {comm_ring_1, ring_no_zero_divisors} poly"
  assumes "\<And>x. x \<in> A \<Longrightarrow> poly p x = poly q x"
  assumes "card A > degree p" "card A > degree q"
  shows   "p = q"
  by sorry

lemma poly_eqI_degree_lead_coeff:
  fixes p q :: "'a :: {comm_ring_1, ring_no_zero_divisors} poly"
  assumes "poly.coeff p n = poly.coeff q n" "card A \<ge> n" "degree p \<le> n" "degree q \<le> n"
  assumes "\<And>z. z \<in> A \<Longrightarrow> poly p z = poly q z"
  shows   "p = q"
  by sorry


subsubsection \<open>Order of polynomial roots\<close>

definition order :: "'a::idom \<Rightarrow> 'a poly \<Rightarrow> nat"
  where "order a p = (LEAST n. \<not> [:-a, 1:] ^ Suc n dvd p)"

lemma coeff_linear_power: "coeff ([:a, 1:] ^ n) n = 1"
  for a :: "'a::comm_semiring_1"
  by sorry

lemma degree_linear_power: "degree ([:a, 1:] ^ n) = n"
  for a :: "'a::comm_semiring_1"
  by sorry

lemma order_1: "[:-a, 1:] ^ order a p dvd p"
  by sorry

lemma order_2:
  assumes "p \<noteq> 0"
  shows "\<not> [:-a, 1:] ^ Suc (order a p) dvd p"
  by sorry

lemma order: "p \<noteq> 0 \<Longrightarrow> [:-a, 1:] ^ order a p dvd p \<and> \<not> [:-a, 1:] ^ Suc (order a p) dvd p"
  by sorry

lemma order_degree:
  assumes p: "p \<noteq> 0"
  shows "order a p \<le> degree p"
  by sorry

lemma order_root: "poly p a = 0 \<longleftrightarrow> p = 0 \<or> order a p \<noteq> 0" (is "?lhs = ?rhs")
  by sorry

lemma order_0I: "poly p a \<noteq> 0 \<Longrightarrow> order a p = 0"
  by sorry

lemma order_unique_lemma:
  fixes p :: "'a::idom poly"
  assumes "[:-a, 1:] ^ n dvd p" "\<not> [:-a, 1:] ^ Suc n dvd p"
  shows "order a p = n"
  by sorry

lemma order_mult:
  assumes "p * q \<noteq> 0" shows "order a (p * q) = order a p + order a q"
  by sorry


lemma order_smult:
  assumes "c \<noteq> 0"
  shows "order x (smult c p) = order x p"
  by sorry

lemma order_gt_0_iff: "p \<noteq> 0 \<Longrightarrow> order x p > 0 \<longleftrightarrow> poly p x = 0"
  by sorry

lemma order_eq_0_iff: "p \<noteq> 0 \<Longrightarrow> order x p = 0 \<longleftrightarrow> poly p x \<noteq> 0"
  by sorry

text \<open>Next three lemmas contributed by Wenda Li\<close>
lemma order_1_eq_0 [simp]:"order x 1 = 0"
  by sorry

lemma order_uminus[simp]: "order x (-p) = order x p"
  by sorry

lemma order_power_n_n: "order a ([:-a,1:]^n)=n"
  by sorry

lemma order_linear[simp]: "order x [:-y, 1:] = (if x=y then 1 else 0)"
  by sorry

lemma order_0_monom [simp]: "c \<noteq> 0 \<Longrightarrow> order 0 (monom c n) = n"
  by sorry

lemma dvd_imp_order_le: "q \<noteq> 0 \<Longrightarrow> p dvd q \<Longrightarrow> Polynomial.order a p \<le> Polynomial.order a q"
  by sorry

text \<open>Now justify the standard squarefree decomposition, i.e. \<open>f / gcd f f'\<close>.\<close>

lemma order_divides: "[:-a, 1:] ^ n dvd p \<longleftrightarrow> p = 0 \<or> n \<le> order a p"
  by sorry

lemma order_decomp:
  assumes "p \<noteq> 0"
  shows "\<exists>q. p = [:- a, 1:] ^ order a p * q \<and> \<not> [:- a, 1:] dvd q"
  by sorry

lemma monom_1_dvd_iff: "p \<noteq> 0 \<Longrightarrow> monom 1 n dvd p \<longleftrightarrow> n \<le> order 0 p"
  by sorry

lemma poly_root_order_induct [case_names 0 no_roots root]:
  fixes p :: "'a :: idom poly"
  assumes "P 0" "\<And>p. (\<And>x. poly p x \<noteq> 0) \<Longrightarrow> P p" 
          "\<And>p x n. n > 0 \<Longrightarrow> poly p x \<noteq> 0 \<Longrightarrow> P p \<Longrightarrow> P ([:-x, 1:] ^ n * p)"
  shows   "P p"
  by sorry


context
  includes multiset.lifting
begin

lift_definition proots :: "('a :: idom) poly \<Rightarrow> 'a multiset" is
  "\<lambda>(p :: 'a poly) (x :: 'a). if p = 0 then 0 else order x p"
proof -
  fix p :: "'a poly"
  show "finite {x. 0 < (if p = 0 then 0 else order x p)}"
    by (cases "p = 0")
       (auto simp: order_gt_0_iff intro: finite_subset[OF _ poly_roots_finite[of p]])
qed

lemma proots_0 [simp]: "proots (0 :: 'a :: idom poly) = {#}"
  by sorry

lemma proots_1 [simp]: "proots (1 :: 'a :: idom poly) = {#}"
  by sorry

lemma proots_const [simp]: "proots [: x :] = 0"
  by sorry

lemma proots_numeral [simp]: "proots (numeral n) = 0"
  by sorry

lemma count_proots [simp]:
  "p \<noteq> 0 \<Longrightarrow> count (proots p) a = order a p"
  by sorry

lemma set_count_proots [simp]:
   "p \<noteq> 0 \<Longrightarrow> set_mset (proots p) = {x. poly p x = 0}"
  by sorry

lemma proots_uminus [simp]: "proots (-p) = proots p"
  by sorry

lemma proots_smult [simp]: "c \<noteq> 0 \<Longrightarrow> proots (smult c p) = proots p"
  by sorry

lemma proots_mult:
  assumes "p \<noteq> 0" "q \<noteq> 0"
  shows   "proots (p * q) = proots p + proots q"
  by sorry

lemma proots_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "proots (\<Prod>x\<in>A. f x) = (\<Sum>x\<in>A. proots (f x))"
  by sorry

lemma proots_prod_mset:
  assumes "0 \<notin># A"
  shows   "proots (\<Prod>p\<in>#A. p) = (\<Sum>p\<in>#A. proots p)"
  by sorry

lemma proots_prod_list:
  assumes "0 \<notin> set ps"
  shows   "proots (\<Prod>p\<leftarrow>ps. p) = (\<Sum>p\<leftarrow>ps. proots p)"
  by sorry

lemma proots_power: "proots (p ^ n) = repeat_mset n (proots p)"
  by sorry

lemma proots_linear_factor [simp]: "proots [:x, 1:] = {#-x#}"
  by sorry

lemma size_proots_le: "size (proots p) \<le> degree p"
  by sorry

end

lemma proots_empty: "proots p = {#} \<longleftrightarrow> p = 0 \<or> (\<forall>x. poly p x \<noteq> 0)"
  by sorry

lemma proots_element: "x \<in># proots p \<or> p = 0 \<longleftrightarrow> poly p x = 0"
  by sorry

subsection \<open>Additional induction rules on polynomials\<close>

text \<open>
  An induction rule for induction over the roots of a polynomial with a certain property.
  (e.g. all positive roots)
\<close>
lemma poly_root_induct [case_names 0 no_roots root]:
  fixes p :: "'a :: idom poly"
  assumes "Q 0"
    and "\<And>p. (\<And>a. P a \<Longrightarrow> poly p a \<noteq> 0) \<Longrightarrow> Q p"
    and "\<And>a p. P a \<Longrightarrow> Q p \<Longrightarrow> Q ([:a, -1:] * p)"
  shows "Q p"
  by sorry

text \<open>Same proof as above. Could they be consolidated?\<close>
lemma poly_root_induct_alt [case_names 0 no_proots root]:
  fixes p :: "'a :: idom poly"
  assumes "Q 0"
  assumes "\<And>p. (\<And>a. P a \<Longrightarrow> poly p a \<noteq> 0) \<Longrightarrow> Q p"
  assumes "\<And>a p. P a \<Longrightarrow> Q p \<Longrightarrow> Q ([:-a, 1:] * p)"
  shows   "Q p"
  by sorry

lemma dropWhile_replicate_append:
  "dropWhile ((=) a) (replicate n a @ ys) = dropWhile ((=) a) ys"
  by sorry

text \<open>
  An induction rule for simultaneous induction over two polynomials,
  prepending one coefficient in each step.
\<close>
lemma poly_induct2 [case_names 0 pCons]:
  assumes "P 0 0" "\<And>a p b q. P p q \<Longrightarrow> P (pCons a p) (pCons b q)"
  shows "P p q"
  by sorry


subsection \<open>Composition of polynomials\<close>

(* Several lemmas contributed by René Thiemann and Akihisa Yamada *)

definition pcompose :: "'a::comm_semiring_0 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "pcompose p q = fold_coeffs (\<lambda>a c. [:a:] + q * c) p 0"

notation pcompose (infixl \<open>\<circ>\<^sub>p\<close> 71)

lemma pcompose_0 [simp]: "pcompose 0 q = 0"
  by sorry

lemma pcompose_pCons: "pcompose (pCons a p) q = [:a:] + q * pcompose p q"
  by sorry

lemma pcompose_altdef: "pcompose p q = poly (map_poly (\<lambda>x. [:x:]) p) q"
  by sorry

lemma coeff_pcompose_0 [simp]:
  "coeff (pcompose p q) 0 = poly p (coeff q 0)"
  by sorry

lemma pcompose_1: "pcompose 1 p = 1"
  for p :: "'a::comm_semiring_1 poly"
  by sorry

lemma poly_pcompose: "poly (pcompose p q) x = poly p (poly q x)"
  by sorry

lemma degree_pcompose_le: "degree (pcompose p q) \<le> degree p * degree q"
  by sorry

lemma pcompose_add: "pcompose (p + q) r = pcompose p r + pcompose q r"
  for p q r :: "'a::{comm_semiring_0, ab_semigroup_add} poly"
  by sorry

lemma pcompose_uminus: "pcompose (-p) r = -pcompose p r"
  for p r :: "'a::comm_ring poly"
  by sorry

lemma pcompose_diff: "pcompose (p - q) r = pcompose p r - pcompose q r"
  for p q r :: "'a::comm_ring poly"
  by sorry

lemma pcompose_smult: "pcompose (smult a p) r = smult a (pcompose p r)"
  for p r :: "'a::comm_semiring_0 poly"
  by sorry

lemma pcompose_mult: "pcompose (p * q) r = pcompose p r * pcompose q r"
  for p q r :: "'a::comm_semiring_0 poly"
  by sorry

lemma pcompose_assoc: "pcompose p (pcompose q r) = pcompose (pcompose p q) r"
  for p q r :: "'a::comm_semiring_0 poly"
  by sorry

lemma pcompose_idR[simp]: "pcompose p [: 0, 1 :] = p"
  for p :: "'a::comm_semiring_1 poly"
  by sorry

lemma pcompose_sum: "pcompose (sum f A) p = sum (\<lambda>i. pcompose (f i) p) A"
  by sorry

lemma pcompose_prod: "pcompose (prod f A) p = prod (\<lambda>i. pcompose (f i) p) A"
  by sorry

lemma pcompose_const [simp]: "pcompose [:a:] q = [:a:]"
  by sorry

lemma pcompose_0': "pcompose p 0 = [:coeff p 0:]"
  by sorry

lemma pcompose_coeff_0:
  "coeff (pcompose p q) 0 = poly p (coeff q 0)"
  by sorry
    
lemma pcompose_pCons_0: "pcompose p [:a:] = [:poly p a:]"
  by sorry
   
lemma degree_pcompose: "degree (pcompose p q) = degree p * degree q"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma pcompose_eq_0:
  fixes p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  assumes "pcompose p q = 0" "degree q > 0"
  shows "p = 0"
  by sorry

lemma pcompose_eq_0_iff:
  fixes p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  assumes "degree q > 0"
  shows "pcompose p q = 0 \<longleftrightarrow> p = 0"
  by sorry

lemma coeff_pcompose_linear:
  "coeff (pcompose p [:0, a :: 'a :: comm_semiring_1:]) i = a ^ i * coeff p i"
  by sorry

lemma lead_coeff_comp:
  fixes p q :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "degree q > 0"
  shows "lead_coeff (pcompose p q) = lead_coeff p * lead_coeff q ^ (degree p)"
  by sorry

lemma coeff_pcompose_monom_linear [simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "coeff (pcompose p (monom c (Suc 0))) k = c ^ k * coeff p k"
  by sorry

lemma of_nat_mult_conv_smult: "of_nat n * P = smult (of_nat n) P"
  by sorry

lemma numeral_mult_conv_smult: "numeral n * P = smult (numeral n) P"
  by sorry

lemma sum_order_le_degree:
  assumes "p \<noteq> 0"
  shows   "(\<Sum>x | poly p x = 0. order x p) \<le> degree p"
  by sorry

subsection \<open>Divisibility\<close>

context
  assumes "SORT_CONSTRAINT('a :: idom)"
begin
lemma poly_linear_linear_factor: 
  assumes dvd: "[:b,1:] dvd (\<Prod> (a :: 'a) \<leftarrow> as. [: a, 1:])"
  shows "b \<in> set as"
  by sorry

lemma poly_linear_exp_linear_factors: 
  assumes dvd: "([:b,1:])^n dvd (\<Prod> (a :: 'a) \<leftarrow> as. [: a, 1:])"
  shows "length (filter ((=) b) as) \<ge> n"
  by sorry
end

lemma const_poly_dvd: "([:a:] dvd [:b:]) = (a dvd b)"
  by sorry

lemma const_poly_dvd_1 [simp]:
  "[:a:] dvd 1 \<longleftrightarrow> a dvd 1"
  by sorry

lemma poly_dvd_1:
  fixes p :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  shows "p dvd 1 \<longleftrightarrow> degree p = 0 \<and> coeff p 0 dvd 1"
  by sorry


subsection \<open>Closure properties of coefficients\<close>

context
  fixes R :: "'a :: comm_semiring_1 set"
  assumes R_0: "0 \<in> R"
  assumes R_plus: "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> x + y \<in> R"
  assumes R_mult: "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> x * y \<in> R"
begin

lemma coeff_mult_semiring_closed:
  assumes "\<And>i. coeff p i \<in> R" "\<And>i. coeff q i \<in> R"
  shows   "coeff (p * q) i \<in> R"
  by sorry

lemma coeff_pcompose_semiring_closed:
  assumes "\<And>i. coeff p i \<in> R" "\<And>i. coeff q i \<in> R"
  shows   "coeff (pcompose p q) i \<in> R"
  by sorry

end


subsection \<open>Shifting polynomials\<close>

definition poly_shift :: "nat \<Rightarrow> 'a::zero poly \<Rightarrow> 'a poly"
  where "poly_shift n p = Abs_poly (\<lambda>i. coeff p (i + n))"

lemma nth_default_drop: "nth_default x (drop n xs) m = nth_default x xs (m + n)"
  by sorry

lemma nth_default_take: "nth_default x (take n xs) m = (if m < n then nth_default x xs m else x)"
  by sorry

lemma coeff_poly_shift: "coeff (poly_shift n p) i = coeff p (i + n)"
  by sorry

lemma poly_shift_id [simp]: "poly_shift 0 = (\<lambda>x. x)"
  by sorry

lemma poly_shift_0 [simp]: "poly_shift n 0 = 0"
  by sorry

lemma poly_shift_1: "poly_shift n 1 = (if n = 0 then 1 else 0)"
  by sorry

lemma poly_shift_monom: "poly_shift n (monom c m) = (if m \<ge> n then monom c (m - n) else 0)"
  by sorry

lemma coeffs_shift_poly [code abstract]:
  "coeffs (poly_shift n p) = drop n (coeffs p)"
  by sorry


subsection \<open>Truncating polynomials\<close>

definition poly_cutoff
  where "poly_cutoff n p = Abs_poly (\<lambda>k. if k < n then coeff p k else 0)"

lemma coeff_poly_cutoff: "coeff (poly_cutoff n p) k = (if k < n then coeff p k else 0)"
  by sorry

lemma poly_cutoff_0 [simp]: "poly_cutoff n 0 = 0"
  by sorry

lemma poly_cutoff_1 [simp]: "poly_cutoff n 1 = (if n = 0 then 0 else 1)"
  by sorry

lemma coeffs_poly_cutoff [code abstract]:
  "coeffs (poly_cutoff n p) = strip_while ((=) 0) (take n (coeffs p))"
  by sorry


subsection \<open>Reflecting polynomials\<close>

definition reflect_poly :: "'a::zero poly \<Rightarrow> 'a poly"
  where "reflect_poly p = Poly (rev (coeffs p))"

lemma coeffs_reflect_poly [code abstract]:
  "coeffs (reflect_poly p) = rev (dropWhile ((=) 0) (coeffs p))"
  by sorry

lemma reflect_poly_0 [simp]: "reflect_poly 0 = 0"
  by sorry

lemma reflect_poly_1 [simp]: "reflect_poly 1 = 1"
  by sorry

lemma coeff_reflect_poly:
  "coeff (reflect_poly p) n = (if n > degree p then 0 else coeff p (degree p - n))"
  by sorry

lemma coeff_0_reflect_poly_0_iff [simp]: "coeff (reflect_poly p) 0 = 0 \<longleftrightarrow> p = 0"
  by sorry

lemma reflect_poly_at_0_eq_0_iff [simp]: "poly (reflect_poly p) 0 = 0 \<longleftrightarrow> p = 0"
  by sorry

lemma reflect_poly_pCons':
  "p \<noteq> 0 \<Longrightarrow> reflect_poly (pCons c p) = reflect_poly p + monom c (Suc (degree p))"
  by sorry

lemma reflect_poly_const [simp]: "reflect_poly [:a:] = [:a:]"
  by sorry

lemma poly_reflect_poly_nz:
  "x \<noteq> 0 \<Longrightarrow> poly (reflect_poly p) x = x ^ degree p * poly p (inverse x)"
  for x :: "'a::field"
  by sorry

lemma coeff_0_reflect_poly [simp]: "coeff (reflect_poly p) 0 = lead_coeff p"
  by sorry

lemma poly_reflect_poly_0 [simp]: "poly (reflect_poly p) 0 = lead_coeff p"
  by sorry

lemma reflect_poly_reflect_poly [simp]: "coeff p 0 \<noteq> 0 \<Longrightarrow> reflect_poly (reflect_poly p) = p"
  by sorry

lemma degree_reflect_poly_le: "degree (reflect_poly p) \<le> degree p"
  by sorry

lemma reflect_poly_pCons: "a \<noteq> 0 \<Longrightarrow> reflect_poly (pCons a p) = Poly (rev (a # coeffs p))"
  by sorry

lemma degree_reflect_poly_eq [simp]: "coeff p 0 \<noteq> 0 \<Longrightarrow> degree (reflect_poly p) = degree p"
  by sorry

lemma reflect_poly_eq_0_iff [simp]: "reflect_poly p = 0 \<longleftrightarrow> p = 0"
  by sorry

(* TODO: does this work with zero divisors as well? Probably not. *)
lemma reflect_poly_mult: "reflect_poly (p * q) = reflect_poly p * reflect_poly q"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma reflect_poly_smult: "reflect_poly (smult c p) = smult c (reflect_poly p)"
  for p :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma reflect_poly_power: "reflect_poly (p ^ n) = reflect_poly p ^ n"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  by sorry

lemma reflect_poly_prod: "reflect_poly (prod f A) = prod (\<lambda>x. reflect_poly (f x)) A"
  for f :: "_ \<Rightarrow> _::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by sorry

lemma reflect_poly_prod_list: "reflect_poly (prod_list xs) = prod_list (map reflect_poly xs)"
  for xs :: "_::{comm_semiring_0,semiring_no_zero_divisors} poly list"
  by sorry

lemma reflect_poly_Poly_nz:
  "no_trailing (HOL.eq 0) xs \<Longrightarrow> reflect_poly (Poly xs) = Poly (rev xs)"
  by sorry

lemmas reflect_poly_simps =
  reflect_poly_0 reflect_poly_1 reflect_poly_const reflect_poly_smult reflect_poly_mult
  reflect_poly_power reflect_poly_prod reflect_poly_prod_list


subsection \<open>Derivatives\<close>

function pderiv :: "('a :: {comm_semiring_1,semiring_no_zero_divisors}) poly \<Rightarrow> 'a poly"
  where "pderiv (pCons a p) = (if p = 0 then 0 else p + pCons 0 (pderiv p))"
  by (auto intro: pCons_cases)

termination pderiv
  by (relation "measure degree") simp_all

declare pderiv.simps[simp del]

lemma pderiv_0 [simp]: "pderiv 0 = 0"
  by sorry

lemma pderiv_pCons: "pderiv (pCons a p) = p + pCons 0 (pderiv p)"
  by sorry

lemma pderiv_1 [simp]: "pderiv 1 = 0"
  by sorry

lemma pderiv_of_nat [simp]: "pderiv (of_nat n) = 0"
  and pderiv_numeral [simp]: "pderiv (numeral m) = 0"
  by sorry

lemma coeff_pderiv: "coeff (pderiv p) n = of_nat (Suc n) * coeff p (Suc n)"
  by sorry

fun pderiv_coeffs_code :: "'a::{comm_semiring_1,semiring_no_zero_divisors} \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "pderiv_coeffs_code f (x # xs) = cCons (f * x) (pderiv_coeffs_code (f+1) xs)"
  | "pderiv_coeffs_code f [] = []"

definition pderiv_coeffs :: "'a::{comm_semiring_1,semiring_no_zero_divisors} list \<Rightarrow> 'a list"
  where "pderiv_coeffs xs = pderiv_coeffs_code 1 (tl xs)"

(* Efficient code for pderiv contributed by René Thiemann and Akihisa Yamada *)
lemma pderiv_coeffs_code:
  "nth_default 0 (pderiv_coeffs_code f xs) n = (f + of_nat n) * nth_default 0 xs n"
  by sorry

lemma coeffs_pderiv_code [code abstract]: "coeffs (pderiv p) = pderiv_coeffs (coeffs p)"
  by sorry

lemma pderiv_eq_0_iff: "pderiv p = 0 \<longleftrightarrow> degree p = 0"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  by sorry

lemma degree_pderiv: "degree (pderiv p) = degree p - 1"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  by sorry

lemma not_dvd_pderiv:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  assumes "degree p \<noteq> 0"
  shows "\<not> p dvd pderiv p"
  by sorry

lemma dvd_pderiv_iff [simp]: "p dvd pderiv p \<longleftrightarrow> degree p = 0"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  by sorry

lemma pderiv_singleton [simp]: "pderiv [:a:] = 0"
  by sorry

lemma pderiv_add: "pderiv (p + q) = pderiv p + pderiv q"
  by sorry

lemma pderiv_minus: "pderiv (- p :: 'a :: idom poly) = - pderiv p"
  by sorry

lemma pderiv_diff: "pderiv ((p :: _ :: idom poly) - q) = pderiv p - pderiv q"
  by sorry

lemma pderiv_smult: "pderiv (smult a p) = smult a (pderiv p)"
  by sorry

lemma pderiv_mult: "pderiv (p * q) = p * pderiv q + q * pderiv p"
  by sorry

lemma pderiv_power_Suc: "pderiv (p ^ Suc n) = smult (of_nat (Suc n)) (p ^ n) * pderiv p"
  by sorry

lemma pderiv_power:
  "pderiv (p ^ n) = smult (of_nat n) (p ^ (n - 1) * pderiv p)"
  by sorry

lemma pderiv_monom:
  "pderiv (monom c n) = monom (of_nat n * c) (n - 1)"
  by sorry

lemma pderiv_pcompose: "pderiv (pcompose p q) = pcompose (pderiv p) q * pderiv q"
  by sorry

lemma pderiv_prod: "pderiv (prod f (as)) = (\<Sum>a\<in>as. prod f (as - {a}) * pderiv (f a))"
  by sorry

lemma lead_coeff_pderiv:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  shows "lead_coeff (pderiv p) = of_nat (degree p) * lead_coeff p"
  by sorry

lemma coeff_higher_pderiv:
  "coeff ((pderiv ^^ m) f) n = pochhammer (of_nat (Suc n)) m * coeff f (n + m)"
  by sorry

lemma higher_pderiv_0 [simp]: "(pderiv ^^ n) 0 = 0"
  by sorry

lemma higher_pderiv_add: "(pderiv ^^ n) (p + q) = (pderiv ^^ n) p + (pderiv ^^ n) q"
  by sorry

lemma higher_pderiv_smult: "(pderiv ^^ n) (smult c p) = smult c ((pderiv ^^ n) p)"
  by sorry

lemma higher_pderiv_monom:
  "m \<le> n + 1 \<Longrightarrow> (pderiv ^^ m) (monom c n) = monom (pochhammer (int n - int m + 1) m * c) (n - m)"
  by sorry

lemma higher_pderiv_monom_eq_zero:
  "m > n + 1 \<Longrightarrow> (pderiv ^^ m) (monom c n) = 0"
  by sorry

lemma higher_pderiv_sum: "(pderiv ^^ n) (sum f A) = (\<Sum>x\<in>A. (pderiv ^^ n) (f x))"
  by sorry

lemma higher_pderiv_sum_mset: "(pderiv ^^ n) (sum_mset A) = (\<Sum>p\<in>#A. (pderiv ^^ n) p)"
  by sorry

lemma higher_pderiv_sum_list: "(pderiv ^^ n) (sum_list ps) = (\<Sum>p\<leftarrow>ps. (pderiv ^^ n) p)"
  by sorry

lemma degree_higher_pderiv: "Polynomial.degree ((pderiv ^^ n) p) = Polynomial.degree p - n"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  by sorry


lemma DERIV_pow2: "DERIV (\<lambda>x. x ^ Suc n) x :> real (Suc n) * (x ^ n)"
  by sorry
declare DERIV_pow2 [simp] DERIV_pow [simp]

lemma DERIV_add_const: "DERIV f x :> D \<Longrightarrow> DERIV (\<lambda>x. a + f x :: 'a::real_normed_field) x :> D"
  by sorry

lemma poly_DERIV [simp]: "DERIV (\<lambda>x. poly p x) x :> poly (pderiv p) x"
  by sorry

lemma poly_isCont[simp]:
  fixes x::"'a::real_normed_field"
  shows "isCont (\<lambda>x. poly p x) x"
  by sorry

lemma tendsto_poly [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. poly p (f x)) \<longlongrightarrow> poly p a) F"
  for f :: "_ \<Rightarrow> 'a::real_normed_field"
  by sorry

lemma continuous_within_poly: "continuous (at z within s) (poly p)"
  for z :: "'a::{real_normed_field}"
  by sorry

lemma continuous_poly [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. poly p (f x))"
  for f :: "_ \<Rightarrow> 'a::real_normed_field"
  by sorry

lemma continuous_on_poly [continuous_intros]:
  fixes p :: "'a :: {real_normed_field} poly"
  assumes "continuous_on A f"
  shows "continuous_on A (\<lambda>x. poly p (f x))"
  by sorry

text \<open>Consequences of the derivative theorem above.\<close>

lemma poly_differentiable[simp]: "(\<lambda>x. poly p x) differentiable (at x)"
  for x :: real
  by sorry

lemma poly_IVT_pos: "a < b \<Longrightarrow> poly p a < 0 \<Longrightarrow> 0 < poly p b \<Longrightarrow> \<exists>x. a < x \<and> x < b \<and> poly p x = 0"
  for a b :: real
  by sorry

lemma poly_IVT_neg: "a < b \<Longrightarrow> 0 < poly p a \<Longrightarrow> poly p b < 0 \<Longrightarrow> \<exists>x. a < x \<and> x < b \<and> poly p x = 0"
  for a b :: real
  by sorry

lemma poly_IVT: "a < b \<Longrightarrow> poly p a * poly p b < 0 \<Longrightarrow> \<exists>x>a. x < b \<and> poly p x = 0"
  for p :: "real poly"
  by sorry

lemma poly_MVT: "a < b \<Longrightarrow> \<exists>x. a < x \<and> x < b \<and> poly p b - poly p a = (b - a) * poly (pderiv p) x"
  for a b :: real
  by sorry

lemma poly_MVT':
  fixes a b :: real
  assumes "{min a b..max a b} \<subseteq> A"
  shows "\<exists>x\<in>A. poly p b - poly p a = (b - a) * poly (pderiv p) x"
  by sorry

lemma poly_pinfty_gt_lc:
  fixes p :: "real poly"
  assumes "lead_coeff p > 0"
  shows "\<exists>n. \<forall> x \<ge> n. poly p x \<ge> lead_coeff p"
  by sorry

lemma dvd_monic:
  fixes p q:: "'a :: idom poly" 
  assumes monic:"lead_coeff p=1" and "p dvd (smult c q)" and "c\<noteq>0"
  shows "p dvd q" using assms
  by sorry

lemma lemma_order_pderiv1:
  "pderiv ([:- a, 1:] ^ Suc n * q) 
  = [:- a, 1:] ^ Suc n * pderiv q + smult (of_nat (Suc n)) (q * [:- a, 1:] ^ n)"
  by sorry

lemma order_pderiv:
  fixes p::"'a::{idom,semiring_char_0} poly"
  assumes "p\<noteq>0" "poly p x = 0"
  shows "order x p = Suc (order x (pderiv p))" using assms
  by sorry

lemma lemma_order_pderiv:
  fixes p :: "'a :: field_char_0 poly"
  assumes n: "0 < n"
    and pd: "pderiv p \<noteq> 0"
    and pe: "p = [:- a, 1:] ^ n * q"
    and nd: "\<not> [:- a, 1:] dvd q"
  shows "n = Suc (order a (pderiv p))"
  by sorry

lemma poly_squarefree_decomp_order:
  fixes p :: "'a::field_char_0 poly"
  assumes "pderiv p \<noteq> 0"
    and p: "p = q * d"
    and p': "pderiv p = e * d"
    and d: "d = r * p + s * pderiv p"
  shows "order a q = (if order a p = 0 then 0 else 1)"
  by sorry

lemma poly_squarefree_decomp_order2:
  "pderiv p \<noteq> 0 \<Longrightarrow> p = q * d \<Longrightarrow> pderiv p = e * d \<Longrightarrow>
    d = r * p + s * pderiv p \<Longrightarrow> \<forall>a. order a q = (if order a p = 0 then 0 else 1)"
  for p :: "'a::field_char_0 poly"
  by sorry

lemma order_pderiv2:
  "pderiv p \<noteq> 0 \<Longrightarrow> order a p \<noteq> 0 \<Longrightarrow> order a (pderiv p) = n \<longleftrightarrow> order a p = Suc n"
  for p :: "'a::field_char_0 poly"
  by sorry

definition rsquarefree :: "'a::idom poly \<Rightarrow> bool"
  where "rsquarefree p \<longleftrightarrow> p \<noteq> 0 \<and> (\<forall>a. order a p = 0 \<or> order a p = 1)"

lemma pderiv_iszero: "pderiv p = 0 \<Longrightarrow> \<exists>h. p = [:h:]"
  for p :: "'a::{semidom,semiring_char_0} poly"
  by sorry

lemma rsquarefree_roots: "rsquarefree p \<longleftrightarrow> (\<forall>a. \<not> (poly p a = 0 \<and> poly (pderiv p) a = 0))"
  for p :: "'a::field_char_0 poly"
  by sorry

lemma rsquarefree_root_order:
  assumes "rsquarefree p" "poly p z = 0"
  shows   "order z p = 1"
  by sorry

lemma poly_squarefree_decomp:
  fixes p :: "'a::field_char_0 poly"
  assumes "pderiv p \<noteq> 0"
    and "p = q * d"
    and "pderiv p = e * d"
    and "d = r * p + s * pderiv p"
  shows "rsquarefree q \<and> (\<forall>a. poly q a = 0 \<longleftrightarrow> poly p a = 0)"
  by sorry

lemma has_field_derivative_poly [derivative_intros]:
  assumes "(f has_field_derivative f') (at x within A)"
  shows   "((\<lambda>x. poly p (f x)) has_field_derivative
             (f' * poly (pderiv p) (f x))) (at x within A)"
  by sorry

lemma rsquarefree_single_root[simp]: "rsquarefree [:-x,1:]"
  by sorry

lemma rsquarefree_mul:
  assumes "rsquarefree p" "rsquarefree q"
    "\<forall> x. poly p x \<noteq> 0 \<or> poly q x \<noteq> 0"
  shows "rsquarefree(p * q)"
  by sorry


subsection \<open>Algebraic numbers\<close>


lemma intpolyE:
  assumes "\<And>i. poly.coeff p i \<in> \<int>"
  obtains q where "p = map_poly of_int q"
  by sorry

lemma ratpolyE:
  assumes "\<And>i. poly.coeff p i \<in> \<rat>"
  obtains q where "p = map_poly of_rat q"
  by sorry

text \<open>
  Algebraic numbers can be defined in two equivalent ways: all real numbers that are
  roots of rational polynomials or of integer polynomials. The Algebraic-Numbers AFP entry
  uses the rational definition, but we need the integer definition.

  The equivalence is obvious since any rational polynomial can be multiplied with the
  LCM of its coefficients, yielding an integer polynomial with the same roots.
\<close>

definition algebraic :: "'a :: field_char_0 \<Rightarrow> bool"
  where "algebraic x \<longleftrightarrow> (\<exists>p. (\<forall>i. coeff p i \<in> \<int>) \<and> p \<noteq> 0 \<and> poly p x = 0)"

lemma algebraicI: "(\<And>i. coeff p i \<in> \<int>) \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> poly p x = 0 \<Longrightarrow> algebraic x"
  by sorry

lemma algebraicE:
  assumes "algebraic x"
  obtains p where "\<And>i. coeff p i \<in> \<int>" "p \<noteq> 0" "poly p x = 0"
  by sorry

lemma algebraic_altdef: "algebraic x \<longleftrightarrow> (\<exists>p. (\<forall>i. coeff p i \<in> \<rat>) \<and> p \<noteq> 0 \<and> poly p x = 0)"
  for p :: "'a::field_char_0 poly"
  by sorry

lemma algebraicI': "(\<And>i. coeff p i \<in> \<rat>) \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> poly p x = 0 \<Longrightarrow> algebraic x"
  by sorry

lemma algebraicE':
  assumes "algebraic (x :: 'a :: field_char_0)"
  obtains p where "p \<noteq> 0" "poly (map_poly of_int p) x = 0"
  by sorry

lemma algebraicE'_nonzero:
  assumes "algebraic (x :: 'a :: field_char_0)" "x \<noteq> 0"
  obtains p where "p \<noteq> 0" "coeff p 0 \<noteq> 0" "poly (map_poly of_int p) x = 0"
  by sorry

lemma rat_imp_algebraic: "x \<in> \<rat> \<Longrightarrow> algebraic x"
  by sorry

lemma algebraic_0 [simp, intro]: "algebraic 0"
  and algebraic_1 [simp, intro]: "algebraic 1"
  and algebraic_numeral [simp, intro]: "algebraic (numeral n)"
  and algebraic_of_nat [simp, intro]: "algebraic (of_nat k)"
  and algebraic_of_int [simp, intro]: "algebraic (of_int m)"
  by sorry

lemma algebraic_ii [simp, intro]: "algebraic \<i>"
  by sorry

lemma algebraic_minus [intro]:
  assumes "algebraic x"
  shows   "algebraic (-x)"
  by sorry

lemma algebraic_minus_iff [simp]:
  "algebraic (-x) \<longleftrightarrow> algebraic (x :: 'a :: field_char_0)"
  by sorry

lemma algebraic_inverse [intro]:
  assumes "algebraic x"
  shows   "algebraic (inverse x)"
  by sorry

lemma algebraic_root:
  assumes "algebraic y"
      and "poly p x = y" and "\<forall>i. coeff p i \<in> \<int>" and "lead_coeff p = 1" and "degree p > 0"
  shows   "algebraic x"
  by sorry

lemma algebraic_abs_real [simp]:
  "algebraic \<bar>x :: real\<bar> \<longleftrightarrow> algebraic x"
  by sorry

lemma algebraic_nth_root_real [intro]:
  assumes "algebraic x"
  shows   "algebraic (root n x)"
  by sorry

lemma algebraic_sqrt [intro]: "algebraic x \<Longrightarrow> algebraic (sqrt x)"
  by sorry

lemma algebraic_csqrt [intro]: "algebraic x \<Longrightarrow> algebraic (csqrt x)"
  by sorry

lemma algebraic_cnj [intro]:
  assumes "algebraic x"
  shows   "algebraic (cnj x)"
  by sorry

lemma algebraic_cnj_iff [simp]: "algebraic (cnj x) \<longleftrightarrow> algebraic x"
  by sorry

lemma algebraic_of_real [intro]:
  assumes "algebraic x"
  shows   "algebraic (of_real x)"
  by sorry

lemma algebraic_of_real_iff [simp]:
   "algebraic (of_real x :: 'a :: {real_algebra_1,field_char_0}) \<longleftrightarrow> algebraic x"
  by sorry


subsection \<open>Algebraic integers\<close>

inductive algebraic_int :: "'a :: field \<Rightarrow> bool" where
  "\<lbrakk>lead_coeff p = 1; \<forall>i. coeff p i \<in> \<int>; poly p x = 0\<rbrakk> \<Longrightarrow> algebraic_int x"

lemma algebraic_int_altdef_ipoly:
  fixes x :: "'a :: field_char_0"
  shows "algebraic_int x \<longleftrightarrow> (\<exists>p. poly (map_poly of_int p) x = 0 \<and> lead_coeff p = 1)"
  by sorry

theorem rational_algebraic_int_is_int:
  assumes "algebraic_int x" and "x \<in> \<rat>"
  shows   "x \<in> \<int>"
  by sorry

lemma algebraic_int_imp_algebraic [dest]: "algebraic_int x \<Longrightarrow> algebraic x"
  by sorry

lemma int_imp_algebraic_int:
  assumes "x \<in> \<int>"
  shows   "algebraic_int x"
  by sorry

lemma algebraic_int_0 [simp, intro]: "algebraic_int 0"
  and algebraic_int_1 [simp, intro]: "algebraic_int 1"
  and algebraic_int_numeral [simp, intro]: "algebraic_int (numeral n)"
  and algebraic_int_of_nat [simp, intro]: "algebraic_int (of_nat k)"
  and algebraic_int_of_int [simp, intro]: "algebraic_int (of_int m)"
  by sorry

lemma algebraic_int_ii [simp, intro]: "algebraic_int \<i>"
  by sorry

lemma algebraic_int_minus [intro]:
  assumes "algebraic_int x"
  shows   "algebraic_int (-x)"
  by sorry

lemma algebraic_int_minus_iff [simp]:
  "algebraic_int (-x) \<longleftrightarrow> algebraic_int (x :: 'a :: field_char_0)"
  by sorry

lemma algebraic_int_inverse [intro]:
  assumes "poly p x = 0" and "\<forall>i. coeff p i \<in> \<int>" and "coeff p 0 = 1"
  shows   "algebraic_int (inverse x)"
  by sorry

lemma algebraic_int_root:
  assumes "algebraic_int y"
      and "poly p x = y" and "\<forall>i. coeff p i \<in> \<int>" and "lead_coeff p = 1" and "degree p > 0"
  shows   "algebraic_int x"
  by sorry

lemma algebraic_int_abs_real [simp]:
  "algebraic_int \<bar>x :: real\<bar> \<longleftrightarrow> algebraic_int x"
  by sorry

lemma algebraic_int_nth_root_real [intro]:
  assumes "algebraic_int x"
  shows   "algebraic_int (root n x)"
  by sorry

lemma algebraic_int_sqrt [intro]: "algebraic_int x \<Longrightarrow> algebraic_int (sqrt x)"
  by sorry

lemma algebraic_int_csqrt [intro]: "algebraic_int x \<Longrightarrow> algebraic_int (csqrt x)"
  by sorry

lemma algebraic_int_cnj [intro]:
  assumes "algebraic_int x"
  shows   "algebraic_int (cnj x)"
  by sorry

lemma algebraic_int_cnj_iff [simp]: "algebraic_int (cnj x) \<longleftrightarrow> algebraic_int x"
  by sorry

lemma algebraic_int_of_real [intro]:
  assumes "algebraic_int x"
  shows   "algebraic_int (of_real x)"
  by sorry

lemma algebraic_int_of_real_iff [simp]:
  "algebraic_int (of_real x :: 'a :: {field_char_0, real_algebra_1}) \<longleftrightarrow> algebraic_int x"
  by sorry


subsection \<open>Division of polynomials\<close>

subsubsection \<open>Division in general\<close>

instantiation poly :: (idom_divide) idom_divide
begin

fun divide_poly_main :: "'a \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly"
  where
    "divide_poly_main lc q r d dr (Suc n) =
      (let cr = coeff r dr; a = cr div lc; mon = monom a n in
        if False \<or> a * lc = cr then \<comment> \<open>\<open>False \<or>\<close> is only because of problem in function-package\<close>
          divide_poly_main
            lc
            (q + mon)
            (r - mon * d)
            d (dr - 1) n else 0)"
  | "divide_poly_main lc q r d dr 0 = q"

definition divide_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "divide_poly f g =
    (if g = 0 then 0
     else
      divide_poly_main (coeff g (degree g)) 0 f g (degree f)
        (1 + length (coeffs f) - length (coeffs g)))"

lemma divide_poly_main:
  assumes d: "d \<noteq> 0" "lc = coeff d (degree d)"
    and "degree (d * r) \<le> dr" "divide_poly_main lc q (d * r) d dr n = q'"
    and "n = 1 + dr - degree d \<or> dr = 0 \<and> n = 0 \<and> d * r = 0"
  shows "q' = q + r"
  by sorry

lemma divide_poly_main_0: "divide_poly_main 0 0 r d dr n = 0"
  by sorry

lemma divide_poly:
  assumes g: "g \<noteq> 0"
  shows "(f * g) div g = (f :: 'a poly)"
  by sorry

lemma divide_poly_0: "f div 0 = 0"
  for f :: "'a poly"
  by sorry

instance
  by standard (auto simp: divide_poly divide_poly_0)

end

instance poly :: (idom_divide) algebraic_semidom ..

lemma div_const_poly_conv_map_poly:
  assumes "[:c:] dvd p"
  shows "p div [:c:] = map_poly (\<lambda>x. x div c) p"
  by sorry

lemma is_unit_monom_0:
  fixes a :: "'a::field"
  assumes "a \<noteq> 0"
  shows "is_unit (monom a 0)"
  by sorry

lemma is_unit_triv: "a \<noteq> 0 \<Longrightarrow> is_unit [:a:]"
  for a :: "'a::field"
  by sorry

lemma is_unit_iff_degree:
  fixes p :: "'a::field poly"
  assumes "p \<noteq> 0"
  shows "is_unit p \<longleftrightarrow> degree p = 0"
    (is "?lhs \<longleftrightarrow> ?rhs")
  by sorry

lemma is_unit_pCons_iff: "is_unit (pCons a p) \<longleftrightarrow> p = 0 \<and> a \<noteq> 0"
  for p :: "'a::field poly"
  by sorry

lemma is_unit_monom_trivial: "is_unit p \<Longrightarrow> monom (coeff p (degree p)) 0 = p"
  for p :: "'a::field poly"
  by sorry

lemma is_unit_const_poly_iff: "[:c:] dvd 1 \<longleftrightarrow> c dvd 1"
  for c :: "'a::{comm_semiring_1,semiring_no_zero_divisors}"
  by sorry

lemma is_unit_polyE:
  fixes p :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "p dvd 1"
  obtains c where "p = [:c:]" "c dvd 1"
  by sorry

lemma is_unit_polyE':
  fixes p :: "'a::field poly"
  assumes "is_unit p"
  obtains a where "p = monom a 0" and "a \<noteq> 0"
  by sorry

lemma is_unit_poly_iff: "p dvd 1 \<longleftrightarrow> (\<exists>c. p = [:c:] \<and> c dvd 1)"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  by sorry

lemma coprime_poly_0:
  "poly p x \<noteq> 0 \<or> poly q x \<noteq> 0" if "coprime p q"
  for x :: "'a :: field"
  by sorry
      
lemma root_imp_reducible_poly:
  fixes x :: "'a :: field"
  assumes "poly p x = 0" and "degree p > 1"
  shows   "\<not>irreducible p"
  by sorry

lemma reducible_polyI:
  fixes p :: "'a :: field poly"
  assumes "p = q * r" "degree q > 0" "degree r > 0"
  shows   "\<not>irreducible p"
  by sorry


subsubsection \<open>Pseudo-Division\<close>

text \<open>This part is by René Thiemann and Akihisa Yamada.\<close>

fun pseudo_divmod_main ::
  "'a :: comm_ring_1  \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly \<times> 'a poly"
  where
    "pseudo_divmod_main lc q r d dr (Suc n) =
      (let
        rr = smult lc r;                                       
        qq = coeff r dr;
        rrr = rr - monom qq n * d;
        qqq = smult lc q + monom qq n
       in pseudo_divmod_main lc qqq rrr d (dr - 1) n)"
  | "pseudo_divmod_main lc q r d dr 0 = (q,r)"

definition pseudo_divmod :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly"
  where "pseudo_divmod p q \<equiv>
    if q = 0 then (0, p)
    else
      pseudo_divmod_main (coeff q (degree q)) 0 p q (degree p)
        (1 + length (coeffs p) - length (coeffs q))"

lemma pseudo_divmod_main:
  assumes d: "d \<noteq> 0" "lc = coeff d (degree d)"
    and "degree r \<le> dr" "pseudo_divmod_main lc q r d dr n = (q',r')"
    and "n = 1 + dr - degree d \<or> dr = 0 \<and> n = 0 \<and> r = 0"
  shows "(r' = 0 \<or> degree r' < degree d) \<and> smult (lc^n) (d * q + r) = d * q' + r'"
  by sorry

lemma pseudo_divmod:
  assumes g: "g \<noteq> 0"
    and *: "pseudo_divmod f g = (q,r)"
  shows "smult (coeff g (degree g) ^ (Suc (degree f) - degree g)) f = g * q + r"  (is ?A)
    and "r = 0 \<or> degree r < degree g"  (is ?B)
  by sorry

definition "pseudo_mod_main lc r d dr n = snd (pseudo_divmod_main lc 0 r d dr n)"

lemma snd_pseudo_divmod_main:
  "snd (pseudo_divmod_main lc q r d dr n) = snd (pseudo_divmod_main lc q' r d dr n)"
  by sorry

definition pseudo_mod :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "pseudo_mod f g = snd (pseudo_divmod f g)"

lemma pseudo_mod:
  fixes f g :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly"
  defines "r \<equiv> pseudo_mod f g"
  assumes g: "g \<noteq> 0"
  shows "\<exists>a q. a \<noteq> 0 \<and> smult a f = g * q + r" "r = 0 \<or> degree r < degree g"
  by sorry

lemma fst_pseudo_divmod_main_as_divide_poly_main:
  assumes d: "d \<noteq> 0"
  defines lc: "lc \<equiv> coeff d (degree d)"
  shows "fst (pseudo_divmod_main lc q r d dr n) =
    divide_poly_main lc (smult (lc^n) q) (smult (lc^n) r) d dr n"
  by sorry


subsubsection \<open>Division in polynomials over fields\<close>

lemma pseudo_divmod_field:
  fixes g :: "'a::field poly"
  assumes g: "g \<noteq> 0"
    and *: "pseudo_divmod f g = (q,r)"
  defines "c \<equiv> coeff g (degree g) ^ (Suc (degree f) - degree g)"
  shows "f = g * smult (1/c) q + smult (1/c) r"
  by sorry

lemma divide_poly_main_field:
  fixes d :: "'a::field poly"
  assumes d: "d \<noteq> 0"
  defines lc: "lc \<equiv> coeff d (degree d)"
  shows "divide_poly_main lc q r d dr n =
    fst (pseudo_divmod_main lc (smult ((1 / lc)^n) q) (smult ((1 / lc)^n) r) d dr n)"
  by sorry

lemma divide_poly_field:
  fixes f g :: "'a::field poly"
  defines "f' \<equiv> smult ((1 / coeff g (degree g)) ^ (Suc (degree f) - degree g)) f"
  shows "f div g = fst (pseudo_divmod f' g)"
  by sorry

instantiation poly :: ("{semidom_divide_unit_factor,idom_divide}") normalization_semidom
begin

definition unit_factor_poly :: "'a poly \<Rightarrow> 'a poly"
  where "unit_factor_poly p = [:unit_factor (lead_coeff p):]"

definition normalize_poly :: "'a poly \<Rightarrow> 'a poly"
  where "normalize p = p div [:unit_factor (lead_coeff p):]"

instance
proof
  fix p :: "'a poly"
  show "unit_factor p * normalize p = p"
  proof (cases "p = 0")
    case True
    then show ?thesis
      by (simp add: unit_factor_poly_def normalize_poly_def)
  next
    case False
    then have "lead_coeff p \<noteq> 0"
      by simp
    then have *: "unit_factor (lead_coeff p) \<noteq> 0"
      using unit_factor_is_unit [of "lead_coeff p"] by auto
    then have "unit_factor (lead_coeff p) dvd 1"
      by (auto intro: unit_factor_is_unit)
    then have **: "unit_factor (lead_coeff p) dvd c" for c
      by (rule dvd_trans) simp
    have ***: "unit_factor (lead_coeff p) * (c div unit_factor (lead_coeff p)) = c" for c
    proof -
      from ** obtain b where "c = unit_factor (lead_coeff p) * b" ..
      with False * show ?thesis by simp
    qed
    have "p div [:unit_factor (lead_coeff p):] =
      map_poly (\<lambda>c. c div unit_factor (lead_coeff p)) p"
      by (simp add: const_poly_dvd_iff div_const_poly_conv_map_poly **)
    then show ?thesis
      by (simp add: normalize_poly_def unit_factor_poly_def
        smult_conv_map_poly map_poly_map_poly o_def ***)
  qed
next
  fix p :: "'a poly"
  assume "is_unit p"
  then obtain c where p: "p = [:c:]" "c dvd 1"
    by (auto simp: is_unit_poly_iff)
  then show "unit_factor p = p"
    by (simp add: unit_factor_poly_def monom_0 is_unit_unit_factor)
next
  fix p :: "'a poly"
  assume "p \<noteq> 0"
  then show "is_unit (unit_factor p)"
    by (simp add: unit_factor_poly_def monom_0 is_unit_poly_iff unit_factor_is_unit)
next
  fix a b :: "'a poly" assume "is_unit a"
  thus "unit_factor (a * b) = a * unit_factor b"
    by (auto simp: unit_factor_poly_def lead_coeff_mult unit_factor_mult elim!: is_unit_polyE)
qed (simp_all add: normalize_poly_def unit_factor_poly_def monom_0 lead_coeff_mult unit_factor_mult)

end

instance poly :: ("{semidom_divide_unit_factor,idom_divide,normalization_semidom_multiplicative}")
  normalization_semidom_multiplicative
  by intro_classes (auto simp: unit_factor_poly_def lead_coeff_mult unit_factor_mult)

lemma normalize_poly_eq_map_poly: "normalize p = map_poly (\<lambda>x. x div unit_factor (lead_coeff p)) p"
  by sorry

lemma coeff_normalize [simp]:
  "coeff (normalize p) n = coeff p n div unit_factor (lead_coeff p)"
  by sorry

lemma lead_coeff_normalize_field:
  fixes p::"'a::{field,semidom_divide_unit_factor} poly"
  assumes "p\<noteq>0"
  shows "lead_coeff (normalize p) = 1"
  by sorry

lemma smult_normalize_field_eq:
  fixes p::"'a::{field,semidom_divide_unit_factor} poly"
  shows "smult (lead_coeff p) (normalize p) = p"
  by sorry

class field_unit_factor = field + unit_factor +
  assumes unit_factor_field [simp]: "unit_factor = id"
begin

subclass semidom_divide_unit_factor
proof
  fix a
  assume "a \<noteq> 0"
  then have "1 = a * inverse a" by simp
  then have "a dvd 1" ..
  then show "unit_factor a dvd 1" by simp
qed simp_all

end

lemma unit_factor_pCons:
  "unit_factor (pCons a p) = (if p = 0 then [:unit_factor a:] else unit_factor p)"
  by sorry

lemma normalize_monom [simp]: "normalize (monom a n) = monom (normalize a) n"
  by sorry

lemma unit_factor_monom [simp]: "unit_factor (monom a n) = [:unit_factor a:]"
  by sorry

lemma normalize_const_poly: "normalize [:c:] = [:normalize c:]"
  by sorry

lemma normalize_smult:
  fixes c :: "'a :: {normalization_semidom_multiplicative, idom_divide}"
  shows "normalize (smult c p) = smult (normalize c) (normalize p)"
  by sorry

instantiation poly :: (field) idom_modulo
begin

definition modulo_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where mod_poly_def: "f mod g =
    (if g = 0 then f else pseudo_mod (smult ((1 / lead_coeff g) ^ (Suc (degree f) - degree g)) f) g)"

instance
proof
  fix x y :: "'a poly"
  show "x div y * y + x mod y = x"
  proof (cases "y = 0")
    case True
    then show ?thesis
      by (simp add: divide_poly_0 mod_poly_def)
  next
    case False
    then have "pseudo_divmod (smult ((1 / lead_coeff y) ^ (Suc (degree x) - degree y)) x) y =
        (x div y, x mod y)"
      by (simp add: divide_poly_field mod_poly_def pseudo_mod_def)
    with False pseudo_divmod [OF False this] show ?thesis
      by (simp add: power_mult_distrib [symmetric] ac_simps)
  qed
qed

end

lemma pseudo_divmod_eq_div_mod:
  \<open>pseudo_divmod f g = (f div g, f mod g)\<close> if \<open>lead_coeff g = 1\<close>
  by sorry

lemma degree_mod_less_degree:
  \<open>degree (x mod y) < degree y\<close> if \<open>y \<noteq> 0\<close> \<open>\<not> y dvd x\<close>
  by sorry

instantiation poly :: (field) unique_euclidean_ring
begin

definition euclidean_size_poly :: "'a poly \<Rightarrow> nat"
  where "euclidean_size_poly p = (if p = 0 then 0 else 2 ^ degree p)"

definition division_segment_poly :: "'a poly \<Rightarrow> 'a poly"
  where [simp]: "division_segment_poly p = 1"

instance proof
  show \<open>(q * p + r) div p = q\<close> if \<open>p \<noteq> 0\<close>
    and \<open>euclidean_size r < euclidean_size p\<close> for q p r :: \<open>'a poly\<close>
  proof (cases \<open>r = 0\<close>)
    case True
    with that show ?thesis
      by simp
  next
    case False
    with \<open>p \<noteq> 0\<close> \<open>euclidean_size r < euclidean_size p\<close>
    have \<open>degree r < degree p\<close>
      by (simp add: euclidean_size_poly_def)
    with \<open>r \<noteq> 0\<close> have \<open>\<not> p dvd r\<close>
      by (auto dest: dvd_imp_degree)
    have \<open>(q * p + r) div p = q \<and> (q * p + r) mod p = r\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      moreover have *: \<open>((q * p + r) div p - q) * p = r - (q * p + r) mod p\<close>
        by (simp add: algebra_simps)
      ultimately have \<open>(q * p + r) div p \<noteq> q\<close> and \<open>(q * p + r) mod p \<noteq> r\<close>
        using \<open>p \<noteq> 0\<close> by auto
      from \<open>\<not> p dvd r\<close> have \<open>\<not> p dvd (q * p + r)\<close>
        by simp
      with \<open>p \<noteq> 0\<close> have \<open>degree ((q * p + r) mod p) < degree p\<close>
        by (rule degree_mod_less_degree)
      with \<open>degree r < degree p\<close> \<open>(q * p + r) mod p \<noteq> r\<close>
      have \<open>degree (r - (q * p + r) mod p) < degree p\<close>
        by (auto intro: degree_diff_less)
      also have \<open>degree p \<le> degree ((q * p + r) div p - q) + degree p\<close>
        by simp
      also from \<open>(q * p + r) div p \<noteq> q\<close> \<open>p \<noteq> 0\<close>
      have \<open>\<dots> = degree (((q * p + r) div p - q) * p)\<close>
        by (simp add: degree_mult_eq)
      also from * have \<open>\<dots> = degree (r - (q * p + r) mod p)\<close>
        by simp
      finally have \<open>degree (r - (q * p + r) mod p) < degree (r - (q * p + r) mod p)\<close> .
      then show False
        by simp
    qed
    then show \<open>(q * p + r) div p = q\<close> ..
  qed
qed (auto simp: euclidean_size_poly_def degree_mult_eq power_add intro: degree_mod_less_degree)

end

lemma euclidean_relation_polyI [case_names by0 divides euclidean_relation]:
  \<open>(x div y, x mod y) = (q, r)\<close>
    if by0: \<open>y = 0 \<Longrightarrow> q = 0 \<and> r = x\<close>
    and divides: \<open>y \<noteq> 0 \<Longrightarrow> y dvd x \<Longrightarrow> r = 0 \<and> x = q * y\<close>
    and euclidean_relation: \<open>y \<noteq> 0 \<Longrightarrow> \<not> y dvd x \<Longrightarrow> degree r < degree y \<and> x = q * y + r\<close>
  by sorry

lemma div_poly_eq_0_iff:
  \<open>x div y = 0 \<longleftrightarrow> x = 0 \<or> y = 0 \<or> degree x < degree y\<close> for x y :: \<open>'a::field poly\<close>
  by sorry

lemma div_poly_less:
  \<open>x div y = 0\<close> if \<open>degree x < degree y\<close> for x y :: \<open>'a::field poly\<close>
  by sorry

lemma mod_poly_less:
  \<open>x mod y = x\<close> if \<open>degree x < degree y\<close>
  by sorry

lemma degree_div_less:
  \<open>degree (x div y) < degree x\<close>
    if \<open>degree x > 0\<close> \<open>degree y > 0\<close>
    for x y :: \<open>'a::field poly\<close>
  by sorry

lemma degree_mod_less': "b \<noteq> 0 \<Longrightarrow> a mod b \<noteq> 0 \<Longrightarrow> degree (a mod b) < degree b"
  by sorry

lemma degree_mod_less: "y \<noteq> 0 \<Longrightarrow> x mod y = 0 \<or> degree (x mod y) < degree y"
  by sorry

lemma div_smult_left: \<open>smult a x div y = smult a (x div y)\<close> (is ?Q)
  and mod_smult_left: \<open>smult a x mod y = smult a (x mod y)\<close> (is ?R)
  for x y :: \<open>'a::field poly\<close>
  by sorry

lemma poly_div_minus_left [simp]: "(- x) div y = - (x div y)"
  for x y :: "'a::field poly"
  by sorry

lemma poly_mod_minus_left [simp]: "(- x) mod y = - (x mod y)"
  for x y :: "'a::field poly"
  by sorry

lemma poly_div_add_left: \<open>(x + y) div z = x div z + y div z\<close> (is ?Q)
  and poly_mod_add_left: \<open>(x + y) mod z = x mod z + y mod z\<close> (is ?R)
  for x y z :: \<open>'a::field poly\<close>
  by sorry

lemma poly_div_diff_left: "(x - y) div z = x div z - y div z"
  for x y z :: "'a::field poly"
  by sorry

lemma poly_mod_diff_left: "(x - y) mod z = x mod z - y mod z"
  for x y z :: "'a::field poly"
  by sorry

lemma div_smult_right: \<open>x div smult a y = smult (inverse a) (x div y)\<close> (is ?Q)
  and mod_smult_right: \<open>x mod smult a y = (if a = 0 then x else x mod y)\<close> (is ?R)
  by sorry

lemma mod_mult_unit_eq:
  \<open>x mod (z * y) = x mod y\<close>
  if \<open>is_unit z\<close>
  for x y z :: \<open>'a::field poly\<close>
  by sorry

lemma poly_div_minus_right [simp]: "x div (- y) = - (x div y)"
  for x y :: "'a::field poly"
  by sorry

lemma poly_mod_minus_right [simp]: "x mod (- y) = x mod y"
  for x y :: "'a::field poly"
  by sorry

lemma poly_div_mult_right: \<open>x div (y * z) = (x div y) div z\<close> (is ?Q)
  and poly_mod_mult_right: \<open>x mod (y * z) = y * (x div y mod z) + x mod y\<close> (is ?R)
  for x y z :: \<open>'a::field poly\<close>
  by sorry

lemma dvd_pCons_imp_dvd_pCons_mod:
  \<open>y dvd pCons a (x mod y)\<close> if \<open>y dvd pCons a x\<close>
  by sorry

lemma degree_less_if_less_eqI:
  \<open>degree x < degree y\<close> if \<open>degree x \<le> degree y\<close> \<open>coeff x (degree y) = 0\<close> \<open>x \<noteq> 0\<close>
  by sorry

lemma div_pCons_eq:
    \<open>pCons a p div q = (if q = 0 then 0 else pCons (coeff (pCons a (p mod q)) (degree q) / lead_coeff q) (p div q))\<close> (is ?Q)
  and mod_pCons_eq:
    \<open>pCons a p mod q = (if q = 0 then pCons a p else pCons a (p mod q) - smult (coeff (pCons a (p mod q)) (degree q) / lead_coeff q) q)\<close> (is ?R)
    for x y :: \<open>'a::field poly\<close>
  by sorry

lemma div_mod_fold_coeffs:
  "(p div q, p mod q) =
    (if q = 0 then (0, p)
     else
      fold_coeffs
        (\<lambda>a (s, r).
          let b = coeff (pCons a r) (degree q) / coeff q (degree q)
          in (pCons b s, pCons a r - smult b q)) p (0, 0))"
  by sorry

lemma mod_pCons:
  fixes a :: "'a::field"
    and x y :: "'a::field poly"
  assumes y: "y \<noteq> 0"
  defines "b \<equiv> coeff (pCons a (x mod y)) (degree y) / coeff y (degree y)"
  shows "(pCons a x) mod y = pCons a (x mod y) - smult b y"
  by sorry


subsubsection \<open>List-based versions for fast implementation\<close>
(* Subsection by:
      Sebastiaan Joosten
      René Thiemann
      Akihisa Yamada
    *)
fun minus_poly_rev_list :: "'a :: group_add list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "minus_poly_rev_list (x # xs) (y # ys) = (x - y) # (minus_poly_rev_list xs ys)"
  | "minus_poly_rev_list xs [] = xs"
  | "minus_poly_rev_list [] (y # ys) = []"

fun pseudo_divmod_main_list ::
  "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list \<times> 'a list"
  where
    "pseudo_divmod_main_list lc q r d (Suc n) =
      (let
        rr = map ((*) lc) r;
        a = hd r;
        qqq = cCons a (map ((*) lc) q);
        rrr = tl (if a = 0 then rr else minus_poly_rev_list rr (map ((*) a) d))
       in pseudo_divmod_main_list lc qqq rrr d n)"
  | "pseudo_divmod_main_list lc q r d 0 = (q, r)"

fun pseudo_mod_main_list :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
    "pseudo_mod_main_list lc r d (Suc n) =
      (let
        rr = map ((*) lc) r;
        a = hd r;
        rrr = tl (if a = 0 then rr else minus_poly_rev_list rr (map ((*) a) d))
       in pseudo_mod_main_list lc rrr d n)"
  | "pseudo_mod_main_list lc r d 0 = r"


fun divmod_poly_one_main_list ::
    "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list \<times> 'a list"
  where
    "divmod_poly_one_main_list q r d (Suc n) =
      (let
        a = hd r;
        qqq = cCons a q;
        rr = tl (if a = 0 then r else minus_poly_rev_list r (map ((*) a) d))
       in divmod_poly_one_main_list qqq rr d n)"
  | "divmod_poly_one_main_list q r d 0 = (q, r)"

fun mod_poly_one_main_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
    "mod_poly_one_main_list r d (Suc n) =
      (let
        a = hd r;
        rr = tl (if a = 0 then r else minus_poly_rev_list r (map ((*) a) d))
       in mod_poly_one_main_list rr d n)"
  | "mod_poly_one_main_list r d 0 = r"

definition pseudo_divmod_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list"
  where "pseudo_divmod_list p q =
    (if q = [] then ([], p)
     else
      (let rq = rev q;
        (qu,re) = pseudo_divmod_main_list (hd rq) [] (rev p) rq (1 + length p - length q)
       in (qu, rev re)))"

definition pseudo_mod_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "pseudo_mod_list p q =
    (if q = [] then p
     else
      (let
        rq = rev q;
        re = pseudo_mod_main_list (hd rq) (rev p) rq (1 + length p - length q)
       in rev re))"

lemma minus_zero_does_nothing: "minus_poly_rev_list x (map ((*) 0) y) = x"
  for x :: "'a::ring list"
  by sorry

lemma length_minus_poly_rev_list [simp]: "length (minus_poly_rev_list xs ys) = length xs"
  by sorry

lemma if_0_minus_poly_rev_list:
  "(if a = 0 then x else minus_poly_rev_list x (map ((*) a) y)) =
    minus_poly_rev_list x (map ((*) a) y)"
  for a :: "'a::ring"
  by sorry

lemma Poly_append: "Poly (a @ b) = Poly a + monom 1 (length a) * Poly b"
  for a :: "'a::comm_semiring_1 list"
  by sorry

lemma minus_poly_rev_list: "length p \<ge> length q \<Longrightarrow>
  Poly (rev (minus_poly_rev_list (rev p) (rev q))) =
    Poly p - monom 1 (length p - length q) * Poly q"
  for p q :: "'a :: comm_ring_1 list"
  by sorry

lemma smult_monom_mult: "smult a (monom b n * f) = monom (a * b) n * f"
  by sorry

lemma head_minus_poly_rev_list:
  "length d \<le> length r \<Longrightarrow> d \<noteq> [] \<Longrightarrow>
    hd (minus_poly_rev_list (map ((*) (last d)) r) (map ((*) (hd r)) (rev d))) = 0"
  for d r :: "'a::comm_ring list"
  by sorry

lemma Poly_map: "Poly (map ((*) a) p) = smult a (Poly p)"
  by sorry

lemma last_coeff_is_hd: "xs \<noteq> [] \<Longrightarrow> coeff (Poly xs) (length xs - 1) = hd (rev xs)"
  by sorry

lemma pseudo_divmod_main_list_invar:
  assumes leading_nonzero: "last d \<noteq> 0"
    and lc: "last d = lc"
    and "d \<noteq> []"
    and "pseudo_divmod_main_list lc q (rev r) (rev d) n = (q', rev r')"
    and "n = 1 + length r - length d"
  shows "pseudo_divmod_main lc (monom 1 n * Poly q) (Poly r) (Poly d) (length r - 1) n =
    (Poly q', Poly r')"
  by sorry

lemma pseudo_divmod_impl [code]:
  "pseudo_divmod f g = map_prod poly_of_list poly_of_list (pseudo_divmod_list (coeffs f) (coeffs g))"
    for f g :: "'a::comm_ring_1 poly"
  by sorry

lemma pseudo_mod_main_list:
  "snd (pseudo_divmod_main_list l q xs ys n) = pseudo_mod_main_list l xs ys n"
  by sorry

lemma pseudo_mod_impl[code]: "pseudo_mod f g = poly_of_list (pseudo_mod_list (coeffs f) (coeffs g))"
  by sorry


subsubsection \<open>Improved Code-Equations for Polynomial (Pseudo) Division\<close>

lemma pdivmod_via_pseudo_divmod:
  \<open>(f div g, f mod g) =
    (if g = 0 then (0, f)
     else
      let
        ilc = inverse (lead_coeff g);
        h = smult ilc g;
        (q,r) = pseudo_divmod f h
      in (smult ilc q, r))\<close>
  (is \<open>?l = ?r\<close>)
  by sorry

lemma pdivmod_via_pseudo_divmod_list:
  "(f div g, f mod g) =
    (let cg = coeffs g in
      if cg = [] then (0, f)
      else
        let
          cf = coeffs f;
          ilc = inverse (last cg);
          ch = map ((*) ilc) cg;
          (q, r) = pseudo_divmod_main_list 1 [] (rev cf) (rev ch) (1 + length cf - length cg)
        in (poly_of_list (map ((*) ilc) q), poly_of_list (rev r)))"
  by sorry

lemma pseudo_divmod_main_list_1: "pseudo_divmod_main_list 1 = divmod_poly_one_main_list"
  by sorry

fun divide_poly_main_list :: "'a::idom_divide \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
    "divide_poly_main_list lc q r d (Suc n) =
      (let
        cr = hd r
        in if cr = 0 then divide_poly_main_list lc (cCons cr q) (tl r) d n else let
        a = cr div lc;
        qq = cCons a q;
        rr = minus_poly_rev_list r (map ((*) a) d)
       in if hd rr = 0 then divide_poly_main_list lc qq (tl rr) d n else [])"
  | "divide_poly_main_list lc q r d 0 = q"

lemma divide_poly_main_list_simp [simp]:
  "divide_poly_main_list lc q r d (Suc n) =
    (let
      cr = hd r;
      a = cr div lc;
      qq = cCons a q;
      rr = minus_poly_rev_list r (map ((*) a) d)
     in if hd rr = 0 then divide_poly_main_list lc qq (tl rr) d n else [])"
  by sorry

declare divide_poly_main_list.simps(1)[simp del]

definition divide_poly_list :: "'a::idom_divide poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "divide_poly_list f g =
    (let cg = coeffs g in
      if cg = [] then g
      else
        let
          cf = coeffs f;
          cgr = rev cg
        in poly_of_list (divide_poly_main_list (hd cgr) [] (rev cf) cgr (1 + length cf - length cg)))"

lemmas pdivmod_via_divmod_list = pdivmod_via_pseudo_divmod_list[unfolded pseudo_divmod_main_list_1]

lemma mod_poly_one_main_list: "snd (divmod_poly_one_main_list q r d n) = mod_poly_one_main_list r d n"
  by sorry

lemma mod_poly_code [code]:
  "f mod g =
    (let cg = coeffs g in
      if cg = [] then f
      else
        let
          cf = coeffs f;
          ilc = inverse (last cg);
          ch = map ((*) ilc) cg;
          r = mod_poly_one_main_list (rev cf) (rev ch) (1 + length cf - length cg)
        in poly_of_list (rev r))"
  (is "_ = ?rhs")
  by sorry

definition div_field_poly_impl :: "'a :: field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "div_field_poly_impl f g =
    (let cg = coeffs g in
      if cg = [] then 0
      else
        let
          cf = coeffs f;
          ilc = inverse (last cg);
          ch = map ((*) ilc) cg;
          q = fst (divmod_poly_one_main_list [] (rev cf) (rev ch) (1 + length cf - length cg))
        in poly_of_list ((map ((*) ilc) q)))"

text \<open>We do not declare the following lemma as code equation, since then polynomial division
  on non-fields will no longer be executable. However, a code-unfold is possible, since
  \<open>div_field_poly_impl\<close> is a bit more efficient than the generic polynomial division.\<close>
lemma div_field_poly_impl[code_unfold]: "(div) = div_field_poly_impl"
  by sorry

lemma divide_poly_main_list:
  assumes lc0: "lc \<noteq> 0"
    and lc: "last d = lc"
    and d: "d \<noteq> []"
    and "n = (1 + length r - length d)"
  shows "Poly (divide_poly_main_list lc q (rev r) (rev d) n) =
    divide_poly_main lc (monom 1 n * Poly q) (Poly r) (Poly d) (length r - 1) n"
  by sorry

lemma divide_poly_list[code]: "f div g = divide_poly_list f g"
  by sorry

lemma poly_mod:
  "poly (p mod q) x = poly p x" if "poly q x = 0"
  by sorry

subsection \<open>Primality and irreducibility in polynomial rings\<close>

lemma prod_mset_const_poly: "(\<Prod>x\<in>#A. [:f x:]) = [:prod_mset (image_mset f A):]"
  by sorry

lemma irreducible_const_poly_iff:
  fixes c :: "'a :: {comm_semiring_1,semiring_no_zero_divisors}"
  shows "irreducible [:c:] \<longleftrightarrow> irreducible c"
  by sorry

lemma lift_prime_elem_poly:
  assumes "prime_elem (c :: 'a :: semidom)"
  shows   "prime_elem [:c:]"
  by sorry

lemma prime_elem_const_poly_iff:
  fixes c :: "'a :: semidom"
  shows   "prime_elem [:c:] \<longleftrightarrow> prime_elem c"
  by sorry


subsection \<open>Content and primitive part of a polynomial\<close>

definition content :: "'a::semiring_gcd poly \<Rightarrow> 'a"
  where "content p = gcd_list (coeffs p)"

lemma content_eq_fold_coeffs [code]: "content p = fold_coeffs gcd p 0"
  by sorry

lemma content_0 [simp]: "content 0 = 0"
  by sorry

lemma content_1 [simp]: "content 1 = 1"
  by sorry

lemma content_const [simp]: "content [:c:] = normalize c"
  by sorry

lemma const_poly_dvd_iff_dvd_content: "[:c:] dvd p \<longleftrightarrow> c dvd content p"
  for c :: "'a::semiring_gcd"
  by sorry

lemma content_dvd [simp]: "[:content p:] dvd p"
  by sorry

lemma content_dvd_coeff [simp]: "content p dvd coeff p n"
  by sorry

lemma content_dvd_coeffs: "c \<in> set (coeffs p) \<Longrightarrow> content p dvd c"
  by sorry

lemma normalize_content [simp]: "normalize (content p) = content p"
  by sorry

lemma is_unit_content_iff [simp]: "is_unit (content p) \<longleftrightarrow> content p = 1"
  by sorry

lemma content_smult [simp]:
  fixes c :: "'a :: {normalization_semidom_multiplicative, semiring_gcd}"
  shows "content (smult c p) = normalize c * content p"
  by sorry

lemma content_eq_zero_iff [simp]: "content p = 0 \<longleftrightarrow> p = 0"
  by sorry

definition primitive_part :: "'a :: semiring_gcd poly \<Rightarrow> 'a poly"
  where "primitive_part p = map_poly (\<lambda>x. x div content p) p"

lemma primitive_part_0 [simp]: "primitive_part 0 = 0"
  by sorry

lemma content_times_primitive_part [simp]: "smult (content p) (primitive_part p) = p"
  for p :: "'a :: semiring_gcd poly"
  by sorry

lemma primitive_part_eq_0_iff [simp]: "primitive_part p = 0 \<longleftrightarrow> p = 0"
  by sorry

lemma content_primitive_part [simp]:
  fixes p :: "'a :: {normalization_semidom_multiplicative, semiring_gcd} poly"
  assumes "p \<noteq> 0"
  shows "content (primitive_part p) = 1"
  by sorry

lemma content_decompose:
  obtains p' :: "'a :: {normalization_semidom_multiplicative, semiring_gcd} poly"
  where "p = smult (content p) p'" "content p' = 1"
  by sorry

lemma content_dvd_contentI [intro]: "p dvd q \<Longrightarrow> content p dvd content q"
  by sorry

lemma primitive_part_const_poly [simp]: "primitive_part [:x:] = [:unit_factor x:]"
  by sorry

lemma primitive_part_prim: "content p = 1 \<Longrightarrow> primitive_part p = p"
  by sorry

lemma degree_primitive_part [simp]: "degree (primitive_part p) = degree p"
  by sorry

lemma smult_content_normalize_primitive_part [simp]:
  fixes p :: "'a :: {normalization_semidom_multiplicative, semiring_gcd, idom_divide} poly"
  shows "smult (content p) (normalize (primitive_part p)) = normalize p"
  by sorry

context
begin

private

lemma content_1_mult:
  fixes f g :: "'a :: {semiring_gcd, factorial_semiring} poly"
  assumes "content f = 1" "content g = 1"
  shows   "content (f * g) = 1"
  by sorry

lemma content_mult:
  fixes p q :: "'a :: {factorial_semiring, semiring_gcd, normalization_semidom_multiplicative} poly"
  shows "content (p * q) = content p * content q"
  by sorry

end

lemma primitive_part_mult:
  fixes p q :: "'a :: {factorial_semiring, semiring_Gcd, ring_gcd, idom_divide,
                       normalization_semidom_multiplicative} poly"
  shows "primitive_part (p * q) = primitive_part p * primitive_part q"
  by sorry

lemma primitive_part_smult:
  fixes p :: "'a :: {factorial_semiring, semiring_Gcd, ring_gcd, idom_divide,
                     normalization_semidom_multiplicative} poly"
  shows "primitive_part (smult a p) = smult (unit_factor a) (primitive_part p)"
  by sorry

lemma primitive_part_dvd_primitive_partI [intro]:
  fixes p q :: "'a :: {factorial_semiring, semiring_Gcd, ring_gcd, idom_divide,
                       normalization_semidom_multiplicative} poly"
  shows "p dvd q \<Longrightarrow> primitive_part p dvd primitive_part q"
  by sorry

lemma content_prod_mset:
  fixes A :: "'a :: {factorial_semiring, semiring_Gcd, normalization_semidom_multiplicative}
      poly multiset"
  shows "content (prod_mset A) = prod_mset (image_mset content A)"
  by sorry

lemma content_prod_eq_1_iff:
  fixes p q :: "'a :: {factorial_semiring, semiring_Gcd, normalization_semidom_multiplicative} poly"
  shows "content (p * q) = 1 \<longleftrightarrow> content p = 1 \<and> content q = 1"
  by sorry


subsection \<open>A typeclass for algebraically closed fields\<close>

(* TODO: Move! *)

text \<open>
  Since the required sort constraints are not available inside the class, we have to resort
  to a somewhat awkward way of writing the definition of algebraically closed fields:
\<close>
class alg_closed_field = field +
  assumes alg_closed: "n > 0 \<Longrightarrow> f n \<noteq> 0 \<Longrightarrow> \<exists>x. (\<Sum>k\<le>n. f k * x ^ k) = 0"

text \<open>
  We can then however easily show the equivalence to the proper definition:
\<close>
lemma alg_closed_imp_poly_has_root:
  assumes "degree (p :: 'a :: alg_closed_field poly) > 0"
  shows   "\<exists>x. poly p x = 0"
  by sorry

lemma alg_closedI [Pure.intro]:
  assumes "\<And>p :: 'a poly. degree p > 0 \<Longrightarrow> lead_coeff p = 1 \<Longrightarrow> \<exists>x. poly p x = 0"
  shows   "OFCLASS('a :: field, alg_closed_field_class)"
  by sorry

lemma (in alg_closed_field) nth_root_exists:
  assumes "n > 0"
  shows   "\<exists>y. y ^ n = (x :: 'a)"
  by sorry

text \<open>
  We can now prove by induction that every polynomial of degree \<open>n\<close> splits into a product of
  \<open>n\<close> linear factors:
\<close>
lemma alg_closed_imp_factorization:
  fixes p :: "'a :: alg_closed_field poly"
  assumes "p \<noteq> 0"
  shows "\<exists>A. size A = degree p \<and> p = smult (lead_coeff p) (\<Prod>x\<in>#A. [:-x, 1:])"
  by sorry

text \<open>
  As an alternative characterisation of algebraic closure, one can also say that any
  polynomial of degree at least 2 splits into non-constant factors:
\<close>
lemma alg_closed_imp_reducible:
  assumes "degree (p :: 'a :: alg_closed_field poly) > 1"
  shows   "\<not>irreducible p"
  by sorry

text \<open>
  When proving algebraic closure through reducibility, we can assume w.l.o.g. that the polynomial
  is monic and has a non-zero constant coefficient:
\<close>
lemma alg_closedI_reducible:
  assumes "\<And>p :: 'a poly. degree p > 1 \<Longrightarrow> lead_coeff p = 1 \<Longrightarrow> coeff p 0 \<noteq> 0 \<Longrightarrow>
              \<not>irreducible p"
  shows   "OFCLASS('a :: field, alg_closed_field_class)"
  by sorry

text \<open>
  Using a clever Tschirnhausen transformation mentioned e.g. in the article by
  Nowak~\<^cite>\<open>"nowak2000"\<close>, we can also assume w.l.o.g. that the coefficient $a_{n-1}$ is zero.
\<close>
lemma alg_closedI_reducible_coeff_deg_minus_one_eq_0:
  assumes "\<And>p :: 'a poly. degree p > 1 \<Longrightarrow> lead_coeff p = 1 \<Longrightarrow> coeff p (degree p - 1) = 0 \<Longrightarrow>
              coeff p 0 \<noteq> 0 \<Longrightarrow> \<not>irreducible p"
  shows   "OFCLASS('a :: field_char_0, alg_closed_field_class)"
  by sorry

text \<open>
  As a consequence of the full factorisation lemma proven above, we can also show that any
  polynomial with at least two different roots splits into two non-constant coprime factors:
\<close>
lemma alg_closed_imp_poly_splits_coprime:
  assumes "degree (p :: 'a :: {alg_closed_field} poly) > 1"
  assumes "poly p x = 0" "poly p y = 0" "x \<noteq> y"
  obtains r s where "degree r > 0" "degree s > 0" "coprime r s" "p = r * s"
  by sorry

subsection \<open>Polynomials and limits\<close>

lemma filterlim_poly_at_infinity:
  fixes p::"'a::real_normed_field poly"
  assumes "degree p>0"
  shows "filterlim (poly p) at_infinity at_infinity"
  by sorry
       
lemma poly_divide_tendsto_aux:
  fixes p::"'a::real_normed_field poly"
  shows "((\<lambda>x. poly p x/x^(degree p)) \<longlongrightarrow> lead_coeff p) at_infinity"  
  by sorry

lemma filterlim_power_at_infinity:
  assumes "n\<noteq>0"
  shows "filterlim (\<lambda>x::'a::real_normed_field. x^n) at_infinity at_infinity" 
  by sorry
   
lemma poly_divide_tendsto_0_at_infinity: 
  fixes p::"'a::real_normed_field poly"
  assumes "degree p > degree q" 
  shows "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> 0 ) at_infinity" 
  by sorry

lemma poly_eventually_not_zero:
  fixes p::"real poly"
  assumes "p\<noteq>0"
  shows "eventually (\<lambda>x. poly p x \<noteq> 0) at_infinity"
  by sorry
    
no_notation cCons (infixr \<open>##\<close> 65)

end
