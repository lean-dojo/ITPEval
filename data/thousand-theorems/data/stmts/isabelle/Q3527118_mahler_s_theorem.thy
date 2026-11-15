(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q3527118 (thousand-theorems__isabelle__Q3527118), "Mahler's theorem":
  the Mahler series of a continuous function on the p-adic integers, with
  coefficients given by iterated forward differences at zero, sums uniformly
  to that function in every complete ultrametric normed module. This file
  contains no proof.
*)

theory Q3527118_mahler_s_theorem
  imports Complex_Main
begin

type_synonym q3527118_padic_int = "nat \<Rightarrow> int"

definition q3527118_prime :: "nat \<Rightarrow> bool" where
  "q3527118_prime p \<longleftrightarrow>
    1 < p \<and> (\<forall>d. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

definition q3527118_padic_valid ::
    "nat \<Rightarrow> q3527118_padic_int \<Rightarrow> bool" where
  "q3527118_padic_valid p x \<longleftrightarrow>
    (\<forall>n. 0 \<le> x n \<and> x n < int (p ^ Suc n)) \<and>
    (\<forall>n m. m \<le> n \<longrightarrow>
      x n mod int (p ^ Suc m) = x m)"

definition q3527118_padic_zero :: q3527118_padic_int where
  "q3527118_padic_zero = (\<lambda>n. 0)"

definition q3527118_padic_nat ::
    "nat \<Rightarrow> nat \<Rightarrow> q3527118_padic_int" where
  "q3527118_padic_nat p a =
    (\<lambda>n. int a mod int (p ^ Suc n))"

definition q3527118_padic_one ::
    "nat \<Rightarrow> q3527118_padic_int" where
  "q3527118_padic_one p = q3527118_padic_nat p 1"

definition q3527118_padic_add ::
    "nat \<Rightarrow> q3527118_padic_int \<Rightarrow> q3527118_padic_int \<Rightarrow>
      q3527118_padic_int" where
  "q3527118_padic_add p x y =
    (\<lambda>n. (x n + y n) mod int (p ^ Suc n))"

definition q3527118_padic_neg ::
    "nat \<Rightarrow> q3527118_padic_int \<Rightarrow> q3527118_padic_int" where
  "q3527118_padic_neg p x =
    (\<lambda>n. (- x n) mod int (p ^ Suc n))"

definition q3527118_padic_sub ::
    "nat \<Rightarrow> q3527118_padic_int \<Rightarrow> q3527118_padic_int \<Rightarrow>
      q3527118_padic_int" where
  "q3527118_padic_sub p x y =
    q3527118_padic_add p x (q3527118_padic_neg p y)"

definition q3527118_padic_mul ::
    "nat \<Rightarrow> q3527118_padic_int \<Rightarrow> q3527118_padic_int \<Rightarrow>
      q3527118_padic_int" where
  "q3527118_padic_mul p x y =
    (\<lambda>n. (x n * y n) mod int (p ^ Suc n))"

definition q3527118_padic_valuation ::
    "q3527118_padic_int \<Rightarrow> nat" where
  "q3527118_padic_valuation x = (LEAST n. x n \<noteq> 0)"

definition q3527118_padic_norm ::
    "nat \<Rightarrow> q3527118_padic_int \<Rightarrow> real" where
  "q3527118_padic_norm p x =
    (if x = q3527118_padic_zero then 0
     else inverse ((real p) ^ q3527118_padic_valuation x))"

definition q3527118_padic_dist ::
    "nat \<Rightarrow> q3527118_padic_int \<Rightarrow> q3527118_padic_int \<Rightarrow>
      real" where
  "q3527118_padic_dist p x y =
    q3527118_padic_norm p (q3527118_padic_sub p x y)"

definition q3527118_complete ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow> bool" where
  "q3527118_complete normE \<longleftrightarrow>
    (\<forall>u :: nat \<Rightarrow> 'e.
      (\<forall>epsilon > 0. \<exists>N. \<forall>m \<ge> N. \<forall>n \<ge> N.
        normE (u m - u n) < epsilon) \<longrightarrow>
      (\<exists>x. \<forall>epsilon > 0. \<exists>N. \<forall>n \<ge> N.
        normE (u n - x) < epsilon))"

definition q3527118_continuous ::
    "nat \<Rightarrow> ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      (q3527118_padic_int \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q3527118_continuous p normE f \<longleftrightarrow>
    (\<forall>x. q3527118_padic_valid p x \<longrightarrow>
      (\<forall>epsilon > 0. \<exists>delta > 0. \<forall>y.
        q3527118_padic_valid p y \<longrightarrow>
        q3527118_padic_dist p y x < delta \<longrightarrow>
        normE (f y - f x) < epsilon))"

definition q3527118_padic_continuous ::
    "nat \<Rightarrow> (q3527118_padic_int \<Rightarrow> q3527118_padic_int) \<Rightarrow>
      bool" where
  "q3527118_padic_continuous p g \<longleftrightarrow>
    (\<forall>x. q3527118_padic_valid p x \<longrightarrow>
      (\<forall>epsilon > 0. \<exists>delta > 0. \<forall>y.
        q3527118_padic_valid p y \<longrightarrow>
        q3527118_padic_dist p y x < delta \<longrightarrow>
        q3527118_padic_dist p (g y) (g x) < epsilon))"

definition q3527118_normed_module ::
    "nat \<Rightarrow> ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      (q3527118_padic_int \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q3527118_normed_module p normE smul \<longleftrightarrow>
    (\<forall>x. 0 \<le> normE x) \<and>
    (\<forall>x. normE x = 0 \<longleftrightarrow> x = 0) \<and>
    (\<forall>x. normE (-x) = normE x) \<and>
    (\<forall>x y. normE (x + y) \<le> max (normE x) (normE y)) \<and>
    q3527118_complete normE \<and>
    (\<forall>x. smul (q3527118_padic_one p) x = x) \<and>
    (\<forall>x. smul q3527118_padic_zero x = 0) \<and>
    (\<forall>a x. q3527118_padic_valid p a \<longrightarrow> smul a 0 = 0) \<and>
    (\<forall>a x y. q3527118_padic_valid p a \<longrightarrow>
      smul a (x + y) = smul a x + smul a y) \<and>
    (\<forall>a b x.
      q3527118_padic_valid p a \<longrightarrow>
      q3527118_padic_valid p b \<longrightarrow>
      smul (q3527118_padic_add p a b) x = smul a x + smul b x) \<and>
    (\<forall>a b x.
      q3527118_padic_valid p a \<longrightarrow>
      q3527118_padic_valid p b \<longrightarrow>
      smul (q3527118_padic_mul p a b) x = smul a (smul b x)) \<and>
    (\<forall>a x. q3527118_padic_valid p a \<longrightarrow>
      normE (smul a x) \<le> q3527118_padic_norm p a * normE x)"

definition q3527118_mahler_characterizes ::
    "nat \<Rightarrow> nat \<Rightarrow>
      (q3527118_padic_int \<Rightarrow> q3527118_padic_int) \<Rightarrow> bool" where
  "q3527118_mahler_characterizes p k g \<longleftrightarrow>
    (\<forall>x. q3527118_padic_valid p x \<longrightarrow>
      q3527118_padic_valid p (g x)) \<and>
    (\<forall>x. \<not> q3527118_padic_valid p x \<longrightarrow>
      g x = q3527118_padic_zero) \<and>
    q3527118_padic_continuous p g \<and>
    (\<forall>m. g (q3527118_padic_nat p m) =
      q3527118_padic_nat p (m choose k))"

definition q3527118_mahler ::
    "nat \<Rightarrow> nat \<Rightarrow> q3527118_padic_int \<Rightarrow>
      q3527118_padic_int" where
  "q3527118_mahler p k =
    (THE g. q3527118_mahler_characterizes p k g)"

primrec q3527118_fwd_diff ::
    "nat \<Rightarrow> (q3527118_padic_int \<Rightarrow> 'e::ab_group_add) \<Rightarrow>
      nat \<Rightarrow> q3527118_padic_int \<Rightarrow> 'e" where
  "q3527118_fwd_diff p f 0 x = f x"
| "q3527118_fwd_diff p f (Suc n) x =
    q3527118_fwd_diff p f n
      (q3527118_padic_add p x (q3527118_padic_one p)) -
    q3527118_fwd_diff p f n x"

definition q3527118_mahler_term ::
    "nat \<Rightarrow>
      (q3527118_padic_int \<Rightarrow> 'e::ab_group_add \<Rightarrow> 'e) \<Rightarrow>
      (q3527118_padic_int \<Rightarrow> 'e) \<Rightarrow>
      nat \<Rightarrow> q3527118_padic_int \<Rightarrow> 'e" where
  "q3527118_mahler_term p smul f n x =
    smul (q3527118_mahler p n x)
      (q3527118_fwd_diff p f n q3527118_padic_zero)"

definition q3527118_has_sum_in_continuous_maps ::
    "nat \<Rightarrow> ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      (nat \<Rightarrow> q3527118_padic_int \<Rightarrow> 'e) \<Rightarrow>
      (q3527118_padic_int \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q3527118_has_sum_in_continuous_maps p normE term f \<longleftrightarrow>
    (\<forall>n. q3527118_continuous p normE (term n)) \<and>
    (\<forall>epsilon > 0. \<exists>S0 :: nat set.
      finite S0 \<and>
      (\<forall>S. finite S \<longrightarrow> S0 \<subseteq> S \<longrightarrow>
        (\<forall>x. q3527118_padic_valid p x \<longrightarrow>
          normE ((\<Sum>n\<in>S. term n x) - f x) < epsilon)))"

theorem hasSum_mahler:
  fixes p :: nat
    and normE :: "'e::ab_group_add \<Rightarrow> real"
    and smul :: "q3527118_padic_int \<Rightarrow> 'e \<Rightarrow> 'e"
    and f :: "q3527118_padic_int \<Rightarrow> 'e"
  assumes prime: "q3527118_prime p"
    and normed_module:
      "q3527118_normed_module TYPE('e) p normE smul"
    and continuous: "q3527118_continuous p normE f"
  shows "q3527118_has_sum_in_continuous_maps p normE
    (q3527118_mahler_term p smul f) f"
  sorry

end
