(* Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com>
   Dedicated to Sandra H. for a wonderful relaxing summer
*)

section \<open>Euler's Partition Theorem\<close>

theory Euler_Partition
imports
  Main
  Card_Number_Partitions.Number_Partition
begin

subsection \<open>Preliminaries\<close>

subsubsection \<open>Additions to Divides Theory\<close>

lemma power_div_nat:
  assumes "c \<le> b"
  assumes "a > 0"
  shows  "(a :: nat) ^ b div a ^ c = a ^ (b - c)"
  by sorry

subsubsection \<open>Additions to Groups-Big Theory\<close>

lemma sum_div:
  assumes "finite A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> (b::'b::euclidean_semiring) dvd f a"
  shows "(\<Sum>a\<in>A. f a) div b = (\<Sum>a\<in>A. (f a) div b)"
  by sorry

lemma sum_mod:
  assumes "finite A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a mod b = (0::'b::unique_euclidean_semiring)"
  shows "(\<Sum>a\<in>A. f a) mod b = 0"
  by sorry

subsubsection \<open>Additions to Finite-Set Theory\<close>

lemma finite_exponents:
  "finite {i. 2 ^ i \<le> (n::nat)}"
  by sorry

subsection \<open>Binary Encoding of Natural Numbers\<close>

definition bitset :: "nat \<Rightarrow> nat set"
where
  "bitset n = {i. odd (n div (2 ^ i))}"

lemma in_bitset_bound:
  "b \<in> bitset n \<Longrightarrow> 2 ^ b \<le> n"
  by sorry

lemma in_bitset_bound_weak:
  "b \<in> bitset n \<Longrightarrow> b \<le> n"
  by sorry

lemma finite_bitset:
  "finite (bitset n)"
  by sorry

lemma bitset_0:
  "bitset 0 = {}"
  by sorry

lemma bitset_2n: "bitset (2 * n) = Suc ` (bitset n)"
  by sorry

lemma bitset_Suc:
  assumes "even n"
  shows "bitset (n + 1) = insert 0 (bitset n)"
  by sorry

lemma bitset_2n1:
  "bitset (2 * n + 1) = insert 0 (Suc ` (bitset n))"
  by sorry

lemma sum_bitset:
  "(\<Sum>i\<in>bitset n. 2 ^ i) = n"
  by sorry

lemma binarysum_div:
  assumes "finite B"
  shows "(\<Sum>i\<in>B. (2::nat) ^ i) div 2 ^ j = (\<Sum>i\<in>B. if i < j then 0 else 2 ^ (i - j))"
  (is "_ = (\<Sum>i\<in>_. ?f i)")
  by sorry

lemma odd_iff:
  assumes "finite B"
  shows "odd (\<Sum>i\<in>B. if i < x then (0::nat) else 2 ^ (i - x)) = (x \<in> B)" (is "odd (\<Sum>i\<in>_. ?s i) = _")
  by sorry

lemma bitset_sum:
  assumes "finite B"
  shows "bitset (\<Sum>i\<in>B. 2 ^ i) = B"
  by sorry

subsection \<open>Decomposition of a Number into a Power of Two and an Odd Number\<close>

function (sequential) index :: "nat \<Rightarrow> nat"
where
  "index 0 = 0"
| "index n = (if odd n then 0 else Suc (index (n div 2)))"
by (pat_completeness) auto

termination
proof
  show "wf {(x::nat, y). x < y}" by (simp add: wf)
next
  fix n show "(Suc n div 2, Suc n) \<in> {(x, y). x < y}" by simp
qed

function (sequential) oddpart :: "nat \<Rightarrow> nat"
where
  "oddpart 0 = 0"
| "oddpart n = (if odd n then n else oddpart (n div 2))"
by pat_completeness auto

termination
proof
  show "wf {(x::nat, y). x < y}" by (simp add: wf)
next
  fix n show "(Suc n div 2, Suc n) \<in> {(x, y). x < y}" by simp
qed

lemma odd_oddpart:
  "odd (oddpart n) \<longleftrightarrow> n \<noteq> 0"
  by sorry

lemma index_oddpart_decomposition:
  "n = 2 ^ (index n) * oddpart n"
  by sorry

lemma oddpart_leq:
  "oddpart n \<le> n"
  by sorry

lemma index_oddpart_unique:
  assumes "odd (m :: nat)" "odd m'"
  shows "(2 ^ i * m = 2 ^ i' * m') \<longleftrightarrow> (i = i' \<and> m = m')"
  by sorry

lemma index_oddpart:
  assumes "odd m"
  shows "index (2 ^ i * m) = i" "oddpart (2 ^ i * m) = m"
  by sorry

subsection \<open>Partitions With Only Distinct and Only Odd Parts\<close>

definition odd_of_distinct :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "odd_of_distinct p = (\<lambda>i. if odd i then (\<Sum>j | p (2 ^ j * i) = 1. 2 ^ j) else 0)"

definition distinct_of_odd :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "distinct_of_odd p = (\<lambda>i. if index i \<in> bitset (p (oddpart i)) then 1 else 0)"

lemma odd:
  "odd_of_distinct p i \<noteq> 0 \<Longrightarrow> odd i"
  by sorry

lemma distinct_distinct_of_odd:
  "distinct_of_odd p i \<le> 1"
  by sorry

lemma odd_of_distinct:
  assumes "odd_of_distinct p i \<noteq> 0"
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> i \<le> n"
  shows "1 \<le> i \<and> i \<le> n"
  by sorry

lemma distinct_of_odd:
  assumes "\<And>i. p i * i \<le> n" "\<And>i. p i \<noteq> 0 \<Longrightarrow> odd i"
  assumes "distinct_of_odd p i \<noteq> 0"
  shows "1 \<le> i \<and> i \<le> n"
  by sorry

lemma odd_distinct:
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> odd i"
  shows "odd_of_distinct (distinct_of_odd p) = p"
  by sorry

lemma distinct_odd:
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> 1 \<le> i \<and> i \<le> n" "\<And>i. p i \<le> 1"
  shows "distinct_of_odd (odd_of_distinct p) = p"
  by sorry

lemma sum_distinct_of_odd:
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> 1 \<le> i \<and> i \<le> n"
  assumes "\<And>i. p i * i \<le> n"
  assumes "\<And>i. p i \<noteq> 0 \<Longrightarrow> odd i"
  shows "(\<Sum>i\<le>n. distinct_of_odd p i * i) = (\<Sum>i\<le>n. p i * i)"
  by sorry

lemma leq_n:
  assumes "\<forall>i. 0 < p i \<longrightarrow> 1 \<le> i \<and> i \<le> (n::nat)"
  assumes "(\<Sum>i\<le>n. p i * i) = n"
  shows "p i * i \<le> n"
  by sorry

lemma distinct_of_odd_in_distinct_partitions:
  assumes "p \<in> {p. p partitions n \<and> (\<forall>i. p i \<noteq> 0 \<longrightarrow> odd i)}"
  shows "distinct_of_odd p \<in> {p. p partitions n \<and> (\<forall>i. p i \<le> 1)}"
  by sorry

lemma odd_of_distinct_in_odd_partitions:
  assumes "p \<in> {p. p partitions n \<and> (\<forall>i. p i \<le> 1)}"
  shows "odd_of_distinct p \<in> {p. p partitions n \<and> (\<forall>i. p i \<noteq> 0 \<longrightarrow> odd i)}"
  by sorry

subsection \<open>Euler's Partition Theorem\<close>

theorem Euler_partition_theorem:
  "card {p. p partitions n \<and> (\<forall>i. p i \<le> 1)} = card {p. p partitions n \<and> (\<forall>i. p i \<noteq> 0 \<longrightarrow> odd i)}"
  (is "card ?distinct_partitions = card ?odd_partitions")
  by sorry

end
