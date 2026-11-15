(*  Title:      HOL/Number_Theory/Quadratic_Reciprocity.thy
    Author:     Jaime Mendizabal Roche
*)

theory Quadratic_Reciprocity
imports Gauss
begin

text \<open>
  The proof is based on Gauss's fifth proof, which can be found at
  \<^url>\<open>https://www.lehigh.edu/~shw2/q-recip/gauss5.pdf\<close>.
\<close>

locale QR =
  fixes p :: "nat"
  fixes q :: "nat"
  assumes p_prime: "prime p"
  assumes p_ge_2: "2 < p"
  assumes q_prime: "prime q"
  assumes q_ge_2: "2 < q"
  assumes pq_neq: "p \<noteq> q"
begin

lemma odd_p: "odd p"
  by sorry

lemma p_ge_0: "0 < int p"
  by sorry
  
lemma p_eq2: "int p = (2 * ((int p - 1) div 2)) + 1"
  by sorry

lemma odd_q: "odd q"
  by sorry

lemma q_ge_0: "0 < int q"
  by sorry

lemma q_eq2: "int q = (2 * ((int q - 1) div 2)) + 1"
  by sorry

lemma pq_eq2: "int p * int q = (2 * ((int p * int q - 1) div 2)) + 1"
  by sorry

lemma pq_coprime: "coprime p q"
  by sorry

lemma pq_coprime_int: "coprime (int p) (int q)"
  by sorry

lemma qp_ineq: "int p * k \<le> (int p * int q - 1) div 2 \<longleftrightarrow> k \<le> (int q - 1) div 2"
  by sorry

lemma QRqp: "QR q p"
  by sorry

lemma pq_commute: "int p * int q = int q * int p"
  by sorry

lemma pq_ge_0: "int p * int q > 0"
  by sorry

definition "r = ((p - 1) div 2) * ((q - 1) div 2)"
definition "m = card (GAUSS.E p q)"
definition "n = card (GAUSS.E q p)"

abbreviation "Res k \<equiv> {0 .. k - 1}" for k :: int
abbreviation "Res_ge_0 k \<equiv> {0 <.. k - 1}" for k :: int
abbreviation "Res_0 k \<equiv> {0::int}" for k :: int
abbreviation "Res_l k \<equiv> {0 <.. (k - 1) div 2}" for k :: int
abbreviation "Res_h k \<equiv> {(k - 1) div 2 <.. k - 1}" for k :: int

abbreviation "Sets_pq r0 r1 r2 \<equiv>
  {(x::int). x \<in> r0 (int p * int q) \<and> x mod p \<in> r1 (int p) \<and> x mod q \<in> r2 (int q)}"

definition "A = Sets_pq Res_l Res_l Res_h"
definition "B = Sets_pq Res_l Res_h Res_l"
definition "C = Sets_pq Res_h Res_h Res_l"
definition "D = Sets_pq Res_l Res_h Res_h"
definition "E = Sets_pq Res_l Res_0 Res_h"
definition "F = Sets_pq Res_l Res_h Res_0"

definition "a = card A"
definition "b = card B"
definition "c = card C"
definition "d = card D"
definition "e = card E"
definition "f = card F"

lemma Gpq: "GAUSS p q"
  by sorry

lemma Gqp: "GAUSS q p"
  by sorry

lemma QR_lemma_01: "(\<lambda>x. x mod q) ` E = GAUSS.E q p"
  by sorry

lemma QR_lemma_02: "e = n"
  by sorry

lemma QR_lemma_03: "f = m"
  by sorry

definition f_1 :: "int \<Rightarrow> int \<times> int"
  where "f_1 x = ((x mod p), (x mod q))"

definition P_1 :: "int \<times> int \<Rightarrow> int \<Rightarrow> bool"
  where "P_1 res x \<longleftrightarrow> x mod p = fst res \<and> x mod q = snd res \<and> x \<in> Res (int p * int q)"

definition g_1 :: "int \<times> int \<Rightarrow> int"
  where "g_1 res = (THE x. P_1 res x)"

lemma P_1_lemma:
  fixes res :: "int \<times> int"
  assumes "0 \<le> fst res" "fst res < p" "0 \<le> snd res" "snd res < q"
  shows "\<exists>!x. P_1 res x"
  by sorry

lemma g_1_lemma:
  fixes res :: "int \<times> int"
  assumes "0 \<le> fst res" "fst res < p" "0 \<le> snd res" "snd res < q"
  shows "P_1 res (g_1 res)"
  by sorry

definition "BuC = Sets_pq Res_ge_0 Res_h Res_l"

lemma finite_BuC [simp]:
  "finite BuC"
  by sorry

lemma QR_lemma_04: "card BuC = card (Res_h p \<times> Res_l q)"
  by sorry

lemma QR_lemma_05: "card (Res_h p \<times> Res_l q) = r"
  by sorry

lemma QR_lemma_06: "b + c = r"
  by sorry

definition f_2:: "int \<Rightarrow> int"
  where "f_2 x = (int p * int q) - x"

lemma f_2_lemma_1: "f_2 (f_2 x) = x"
  by sorry

lemma f_2_lemma_2: "[f_2 x = int p - x] (mod p)"
  by sorry

lemma f_2_lemma_3: "f_2 x \<in> S \<Longrightarrow> x \<in> f_2 ` S"
  by sorry

lemma QR_lemma_07:
  "f_2 ` Res_l (int p * int q) = Res_h (int p * int q)"
  "f_2 ` Res_h (int p * int q) = Res_l (int p * int q)"
  by sorry

lemma QR_lemma_08:
    "f_2 x mod p \<in> Res_l p \<longleftrightarrow> x mod p \<in> Res_h p"
    "f_2 x mod p \<in> Res_h p \<longleftrightarrow> x mod p \<in> Res_l p"
  by sorry

lemma QR_lemma_09:
    "f_2 x mod q \<in> Res_l q \<longleftrightarrow> x mod q \<in> Res_h q"
    "f_2 x mod q \<in> Res_h q \<longleftrightarrow> x mod q \<in> Res_l q"
  by sorry

lemma QR_lemma_10: "a = c"
  by sorry

definition "BuD = Sets_pq Res_l Res_h Res_ge_0"
definition "BuDuF = Sets_pq Res_l Res_h Res"

definition f_3 :: "int \<Rightarrow> int \<times> int"
  where "f_3 x = (x mod p, x div p + 1)"

definition g_3 :: "int \<times> int \<Rightarrow> int"
  where "g_3 x = fst x + (snd x - 1) * p"

lemma QR_lemma_11: "card BuDuF = card (Res_h p \<times> Res_l q)"
  by sorry

lemma QR_lemma_12: "b + d + m = r"
  by sorry

lemma QR_lemma_13: "a + d + n = r"
  by sorry

lemma QR_lemma_14: "(-1::int) ^ (m + n) = (-1) ^ r"
  by sorry

lemma Quadratic_Reciprocity:
  "Legendre p q * Legendre q p = (-1::int) ^ ((p - 1) div 2 * ((q - 1) div 2))"
  by sorry

end

theorem Quadratic_Reciprocity:
  assumes "prime p" "2 < p" "prime q" "2 < q" "p \<noteq> q"
  shows "Legendre p q * Legendre q p = (-1::int) ^ ((p - 1) div 2 * ((q - 1) div 2))"
  by sorry

theorem Quadratic_Reciprocity_int:
  assumes "prime (nat p)" "2 < p" "prime (nat q)" "2 < q" "p \<noteq> q"
  shows "Legendre p q * Legendre q p = (-1::int) ^ (nat ((p - 1) div 2 * ((q - 1) div 2)))"
  by sorry

end
