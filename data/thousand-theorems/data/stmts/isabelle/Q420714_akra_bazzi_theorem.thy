(*
  Statement-only formalization of the thousand-theorems corpus artifact Q420714,
  "Akra–Bazzi theorem": the standard Akra–Bazzi expression is an asymptotic
  upper bound for every recurrence satisfying the theorem's hypotheses.
  This file contains no proof.
*)
theory Q420714_akra_bazzi_theorem
  imports "HOL-Library.Landau_Symbols"
begin

definition q420714_grows_polynomially :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "q420714_grows_polynomially f \<longleftrightarrow>
    (\<forall>b. 0 < b \<and> b < 1 \<longrightarrow>
      (\<exists>c1>0. \<exists>c2>0.
        eventually
          (\<lambda>x. \<forall>u. b * x \<le> u \<and> u \<le> x \<longrightarrow>
            c1 * f x \<le> f u \<and> f u \<le> c2 * f x)
          at_top))"

definition q420714_recurrence ::
    "(nat \<Rightarrow> real) \<Rightarrow>
     (real \<Rightarrow> real) \<Rightarrow>
     ('i::finite \<Rightarrow> real) \<Rightarrow>
     ('i \<Rightarrow> real) \<Rightarrow>
     ('i \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "q420714_recurrence T g a b r \<longleftrightarrow>
    (\<exists>n0. 0 < n0 \<and>
      (\<forall>i. 0 < a i) \<and>
      (\<forall>i. 0 < b i) \<and>
      (\<forall>i. b i < 1) \<and>
      (\<forall>x\<ge>0. 0 \<le> g x) \<and>
      q420714_grows_polynomially g \<and>
      (\<forall>n. n0 \<le> n \<longrightarrow>
        T n = (\<Sum>i\<in>UNIV. a i * T (r i n)) + g (real n)) \<and>
      (\<forall>n<n0. 0 < T n) \<and>
      (\<forall>i n. n0 \<le> n \<longrightarrow> r i n < n) \<and>
      (\<forall>i. (\<lambda>n. real (r i n) - b i * real n)
        \<in> smallo at_top
          (\<lambda>n. real n / (ln (real n)) ^ 2)))"

definition q420714_p ::
    "('i::finite \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> real" where
  "q420714_p a b =
    (THE p. (\<Sum>i\<in>UNIV. a i * (b i powr p)) = 1)"

definition q420714_asymp_bound ::
    "(real \<Rightarrow> real) \<Rightarrow>
     ('i::finite \<Rightarrow> real) \<Rightarrow>
     ('i \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "q420714_asymp_bound g a b n =
    (let p = q420714_p a b
     in real n powr p +
       (real n powr p) *
         (\<Sum>u\<in>{0..<n}. g (real u) / (real u powr (p + 1))))"

theorem q420714_isBigO_asympBound:
  fixes T :: "nat \<Rightarrow> real"
    and g :: "real \<Rightarrow> real"
    and a b :: "'i::finite \<Rightarrow> real"
    and r :: "'i \<Rightarrow> nat \<Rightarrow> nat"
  assumes "q420714_recurrence T g a b r"
  shows "T \<in> bigo at_top (q420714_asymp_bound g a b)"
  sorry

end
