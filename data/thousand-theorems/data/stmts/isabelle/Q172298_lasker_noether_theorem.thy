(*
  Statement-only formalization of thousand-theorems corpus artifact Q172298
  (thousand-theorems__isabelle__Q172298), "Lasker–Noether theorem": a finite
  primary decomposition of a submodule can be replaced by one with the same
  intersection whose primary components have pairwise distinct radical
  annihilator ideals. This file contains no proof.
*)

theory Q172298_lasker_noether_theorem
  imports Main
begin

definition q172298_comm_semiring ::
    "'r::{comm_semiring_0,one} itself \<Rightarrow> bool" where
  "q172298_comm_semiring TYPE('r) \<longleftrightarrow>
    (\<forall>a::'r. 1 * a = a \<and> a * 1 = a)"

fun q172298_pow :: "'r::{one,times} \<Rightarrow> nat \<Rightarrow> 'r" where
  "q172298_pow a 0 = 1"
| "q172298_pow a (Suc n) = a * q172298_pow a n"

definition q172298_module ::
    "('r::{comm_semiring_0,one} \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm)
      \<Rightarrow> bool" where
  "q172298_module smul \<longleftrightarrow>
    (\<forall>x. smul 1 x = x) \<and>
    (\<forall>a b x. smul (a * b) x = smul a (smul b x)) \<and>
    (\<forall>a b x. smul (a + b) x = smul a x + smul b x) \<and>
    (\<forall>a x y. smul a (x + y) = smul a x + smul a y) \<and>
    (\<forall>x. smul 0 x = 0) \<and>
    (\<forall>a. smul a 0 = 0)"

definition q172298_submodule ::
    "('r::{comm_semiring_0,one} \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm) \<Rightarrow>
      'm set \<Rightarrow> bool" where
  "q172298_submodule smul N \<longleftrightarrow>
    0 \<in> N \<and>
    (\<forall>x \<in> N. \<forall>y \<in> N. x + y \<in> N) \<and>
    (\<forall>a. \<forall>x \<in> N. smul a x \<in> N)"

definition q172298_colon ::
    "('r::{comm_semiring_0,one} \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm) \<Rightarrow>
      'm set \<Rightarrow> 'r set" where
  "q172298_colon smul N = {a. \<forall>x. smul a x \<in> N}"

definition q172298_radical ::
    "'r::{comm_semiring_0,one} set \<Rightarrow> 'r set" where
  "q172298_radical I = {a. \<exists>n::nat. q172298_pow a n \<in> I}"

definition q172298_primary ::
    "('r::{comm_semiring_0,one} \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm)
      \<Rightarrow>
      'm set \<Rightarrow> bool" where
  "q172298_primary smul Q \<longleftrightarrow>
    q172298_submodule smul Q \<and>
    Q \<noteq> UNIV \<and>
    (\<forall>a x. smul a x \<in> Q \<longrightarrow>
      x \<in> Q \<or> a \<in> q172298_radical (q172298_colon smul Q))"

theorem primary_decomposition_pairwise_ne_radical:
  fixes smul ::
      "'r::{comm_semiring_0,one} \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm"
    and N :: "'m set"
    and S :: "'m set set"
  assumes "q172298_comm_semiring TYPE('r)"
    and "q172298_module smul"
    and "q172298_submodule smul N"
    and "finite S"
    and "Inter S = N"
    and "\<forall>Q \<in> S. q172298_primary smul Q"
  shows "\<exists>T :: 'm set set.
    finite T \<and>
    Inter T = N \<and>
    (\<forall>Q \<in> T. q172298_primary smul Q) \<and>
    (\<forall>I \<in> T. \<forall>J \<in> T. I \<noteq> J \<longrightarrow>
      q172298_radical (q172298_colon smul I) \<noteq>
        q172298_radical (q172298_colon smul J))"
  sorry

end
