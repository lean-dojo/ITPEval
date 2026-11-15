(*
  Statement-only formalization of thousand-theorems corpus artifact Q1057919,
  "Sylow theorems": existence of prime-power subgroups, conjugacy of Sylow
  subgroups, and the divisibility and congruence properties of their number.
  This file contains no proof.
*)

theory Q1057919_sylow_theorems
  imports Main
begin

definition nat_prime :: "nat \<Rightarrow> bool" where
  "nat_prime p \<longleftrightarrow>
    2 \<le> p \<and> (\<forall>d. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

primrec add_power :: "'g::group_add \<Rightarrow> nat \<Rightarrow> 'g" where
  "add_power x 0 = 0"
| "add_power x (Suc n) = x + add_power x n"

definition is_subgroup :: "'g::group_add set \<Rightarrow> bool" where
  "is_subgroup H \<longleftrightarrow>
    0 \<in> H \<and>
    (\<forall>x \<in> H. - x \<in> H) \<and>
    (\<forall>x \<in> H. \<forall>y \<in> H. x + y \<in> H)"

definition is_p_subgroup :: "nat \<Rightarrow> 'g::group_add set \<Rightarrow> bool" where
  "is_p_subgroup p H \<longleftrightarrow>
    is_subgroup H \<and> (\<forall>x \<in> H. \<exists>n. add_power x (p ^ n) = 0)"

definition is_sylow_subgroup :: "nat \<Rightarrow> 'g::group_add set \<Rightarrow> bool" where
  "is_sylow_subgroup p P \<longleftrightarrow>
    is_p_subgroup p P \<and>
    (\<forall>Q. is_p_subgroup p Q \<longrightarrow> P \<subseteq> Q \<longrightarrow> Q = P)"

definition sylow_subgroups :: "nat \<Rightarrow> 'g::group_add set set" where
  "sylow_subgroups p = {P. is_sylow_subgroup p P}"

definition conjugate_subgroup :: "'g::group_add \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "conjugate_subgroup g H =
    (\<lambda>h. g + h + (- g)) ` H"

definition right_cosets :: "'g::group_add set \<Rightarrow> 'g set set" where
  "right_cosets H = (\<lambda>g. (\<lambda>h. h + g) ` H) ` UNIV"

definition subgroup_index :: "'g::group_add set \<Rightarrow> nat" where
  "subgroup_index H = card (right_cosets H)"

theorem exists_subgroup_card_pow_prime:
  fixes p n :: nat
  assumes "finite (UNIV :: 'g::group_add set)"
    and "nat_prime p"
    and "p ^ n dvd card (UNIV :: 'g set)"
  shows "\<exists>K :: 'g set. is_subgroup K \<and> card K = p ^ n"
  sorry

theorem sylow_is_pretransitive_of_finite:
  fixes p :: nat
  assumes "nat_prime p"
    and "finite (sylow_subgroups p :: 'g::group_add set set)"
  shows "\<forall>P \<in> sylow_subgroups p. \<forall>Q \<in> sylow_subgroups p.
    \<exists>g :: 'g. conjugate_subgroup g P = Q"
  sorry

theorem card_sylow_dvd_index:
  fixes p :: nat
    and P :: "'g::group_add set"
  assumes "nat_prime p"
    and "finite (sylow_subgroups p :: 'g set set)"
    and "P \<in> sylow_subgroups p"
  shows "card (sylow_subgroups p) dvd subgroup_index P"
  sorry

theorem card_sylow_mod_eq_one:
  fixes p :: nat
  assumes "nat_prime p"
    and "finite (sylow_subgroups p :: 'g::group_add set set)"
  shows "card (sylow_subgroups p :: 'g set set) mod p = 1 mod p"
  sorry

end
