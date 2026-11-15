(*
  Statement-only formalization of thousand-theorems corpus artifact Q3527219
  (thousand-theorems__isabelle__Q3527219), "Weierstrass preparation theorem":
  over a commutative local ring complete in its maximal-ideal adic topology,
  a power series nonzero modulo the maximal ideal factors as a distinguished
  polynomial times a unit power series. This file contains no proof.
*)

theory Q3527219_weierstrass_preparation_theorem
  imports Main
begin

definition q3527219_is_unit :: "'a::comm_ring_1 \<Rightarrow> bool" where
  "q3527219_is_unit a \<longleftrightarrow> (\<exists>b. a * b = 1)"

definition q3527219_maximal_ideal :: "'a::comm_ring_1 set" where
  "q3527219_maximal_ideal = {a. \<not> q3527219_is_unit a}"

fun q3527219_ideal_power_member ::
    "'a::comm_ring_1 set \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "q3527219_ideal_power_member I 0 x = True"
| "q3527219_ideal_power_member I (Suc n) x \<longleftrightarrow>
    (\<exists>k (a :: nat \<Rightarrow> 'a) (b :: nat \<Rightarrow> 'a).
      x = (\<Sum>i<k. a i * b i) \<and>
      (\<forall>i<k. a i \<in> I \<and> q3527219_ideal_power_member I n (b i)))"

definition q3527219_is_adic_complete ::
    "'a::comm_ring_1 set \<Rightarrow> bool" where
  "q3527219_is_adic_complete I \<longleftrightarrow>
    (\<forall>x. (\<forall>n. q3527219_ideal_power_member I n x) \<longrightarrow> x = 0) \<and>
    (\<forall>s :: nat \<Rightarrow> 'a.
      (\<forall>m n. m \<le> n \<longrightarrow>
        q3527219_ideal_power_member I m (s m - s n)) \<longrightarrow>
      (\<exists>L. \<forall>n. q3527219_ideal_power_member I n (s n - L)))"

definition q3527219_fps_mul ::
    "(nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow>
      (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "q3527219_fps_mul f h n = (\<Sum>i\<le>n. f i * h (n - i))"

definition q3527219_fps_is_unit ::
    "(nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> bool" where
  "q3527219_fps_is_unit h \<longleftrightarrow>
    (\<exists>k. \<forall>n.
      q3527219_fps_mul h k n = (if n = 0 then 1 else 0))"

definition q3527219_is_distinguished ::
    "'a::comm_ring_1 set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "q3527219_is_distinguished I f \<longleftrightarrow>
    (\<exists>d.
      f d = 1 \<and>
      (\<forall>i>d. f i = 0) \<and>
      (\<forall>i<d. f i \<in> I))"

theorem q3527219_weierstrass_preparation:
  fixes g :: "nat \<Rightarrow> 'a::comm_ring_1"
  assumes nontrivial: "0 \<noteq> (1::'a)"
    and local:
      "\<forall>a b :: 'a. a + b = 1 \<longrightarrow>
        q3527219_is_unit a \<or> q3527219_is_unit b"
    and complete:
      "q3527219_is_adic_complete
        (q3527219_maximal_ideal :: 'a set)"
    and residue_nonzero:
      "\<exists>n. g n \<notin> (q3527219_maximal_ideal :: 'a set)"
  shows "\<exists>f h :: nat \<Rightarrow> 'a.
    q3527219_is_distinguished q3527219_maximal_ideal f \<and>
    q3527219_fps_is_unit h \<and>
    (\<forall>n. g n = q3527219_fps_mul f h n)"
  sorry

end
