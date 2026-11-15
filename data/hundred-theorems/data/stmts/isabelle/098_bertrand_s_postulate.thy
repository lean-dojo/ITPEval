(*
  File:     Bertrand.thy
  Authors:  Julian Biendarra, Manuel Eberl <manuel@pruvisto.org>, Larry Paulson

  A proof of Bertrand's postulate (based on John Harrison's HOL Light proof).
  Uses reflection and the approximation tactic.
*)
theory Bertrand
  imports 
    Complex_Main
    "HOL-Number_Theory.Number_Theory"
    "HOL-Library.Discrete_Functions"
    "HOL-Decision_Procs.Approximation_Bounds"
    "HOL-Library.Code_Target_Numeral"
    Pratt_Certificate.Pratt_Certificate
begin

subsection \<open>Auxiliary facts\<close>
 
lemma ln_2_le: "ln 2 \<le> 355 / (512 :: real)"
  by sorry

lemma ln_2_ge: "ln 2 \<ge> (5677 / 8192 :: real)"
  by sorry

lemma ln_2_ge': "ln (2 :: real) \<ge> 2/3" and ln_2_le': "ln (2 :: real) \<le> 16/23"
  by sorry

lemma of_nat_ge_1_iff: "(of_nat x :: 'a :: linordered_semidom) \<ge> 1 \<longleftrightarrow> x \<ge> 1"
  by sorry
  
lemma floor_conv_div_nat:
  "of_int (floor (real m / real n)) = real (m div n)"
  by sorry

lemma frac_conv_mod_nat:
  "frac (real m / real n) = real (m mod n) / real n"
  by sorry

lemma of_nat_prod_mset: "prod_mset (image_mset of_nat A) = of_nat (prod_mset A)"
  by sorry

lemma prod_mset_pos: "(\<And>x :: 'a :: linordered_semidom. x \<in># A \<Longrightarrow> x > 0) \<Longrightarrow> prod_mset A > 0"
  by sorry

lemma ln_msetprod:
  assumes "\<And>x. x \<in>#I \<Longrightarrow> x > 0"
  shows "(\<Sum>p::nat\<in>#I. ln p) = ln (\<Prod>p\<in>#I. p)"
  by sorry

lemma ln_fact: "ln (fact n) = (\<Sum>d=1..n. ln d)"
  by sorry

lemma overpower_lemma:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f a \<le> g a"
  assumes "\<And>x. a \<le> x \<Longrightarrow> ((\<lambda>x. g x - f x) has_real_derivative (d x)) (at x)"
  assumes "\<And>x. a \<le> x \<Longrightarrow> d x \<ge> 0"
  assumes "a \<le> x"
  shows   "f x \<le> g x"
  by sorry


subsection \<open>Preliminary definitions\<close>

definition primepow_even :: "nat \<Rightarrow> bool" where
  "primepow_even q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^(2*k))"

definition primepow_odd :: "nat \<Rightarrow> bool" where
  "primepow_odd q \<longleftrightarrow> (\<exists> p k. 1 \<le> k \<and> prime p \<and> q = p^(2*k+1))"

abbreviation (input) isprimedivisor :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "isprimedivisor q p \<equiv> prime p \<and> p dvd q"

definition pre_mangoldt :: "nat \<Rightarrow> nat" where
  "pre_mangoldt d = (if primepow d then aprimedivisor d else 1)"

definition mangoldt_even :: "nat \<Rightarrow> real" where
  "mangoldt_even d = (if primepow_even d then ln (real (aprimedivisor d)) else 0)"

definition mangoldt_odd :: "nat \<Rightarrow> real" where
  "mangoldt_odd d = (if primepow_odd d then ln (real (aprimedivisor d)) else 0)"

definition mangoldt_1 :: "nat \<Rightarrow> real" where
  "mangoldt_1 d = (if prime d then ln d else 0)"

definition psi :: "nat \<Rightarrow> real" where
  "psi n = (\<Sum>d=1..n. mangoldt d)"

definition psi_even :: "nat \<Rightarrow> real" where
  "psi_even n = (\<Sum>d=1..n. mangoldt_even d)"

definition psi_odd :: "nat \<Rightarrow> real" where
  "psi_odd n = (\<Sum>d=1..n. mangoldt_odd d)"

abbreviation (input) psi_even_2 :: "nat \<Rightarrow> real" where
  "psi_even_2 n \<equiv> (\<Sum>d=2..n. mangoldt_even d)"

abbreviation (input) psi_odd_2 :: "nat \<Rightarrow> real" where
  "psi_odd_2 n \<equiv> (\<Sum>d=2..n. mangoldt_odd d)"

definition theta :: "nat \<Rightarrow> real" where
  "theta n = (\<Sum>p=1..n. if prime p then ln (real p) else 0)"

subsection \<open>Properties of prime powers\<close>  

lemma primepow_even_imp_primepow:
  assumes "primepow_even n"
  shows   "primepow n"
  by sorry

lemma primepow_odd_imp_primepow:
  assumes "primepow_odd n"
  shows   "primepow n"
  by sorry

lemma primepow_odd_altdef:
  "primepow_odd n \<longleftrightarrow>
     primepow n \<and> odd (multiplicity (aprimedivisor n) n) \<and> multiplicity (aprimedivisor n) n > 1"
  by sorry

lemma primepow_even_altdef:
  "primepow_even n \<longleftrightarrow> primepow n \<and> even (multiplicity (aprimedivisor n) n)"
  by sorry

lemma primepow_odd_mult:
  assumes "d > Suc 0"
  shows   "primepow_odd (aprimedivisor d * d) \<longleftrightarrow> primepow_even d"
  by sorry

lemma pre_mangoldt_primepow:
  assumes "primepow n" "aprimedivisor n = p"
  shows   "pre_mangoldt n = p"
  by sorry

lemma pre_mangoldt_notprimepow:
  assumes "\<not>primepow n"
  shows   "pre_mangoldt n = 1"
  by sorry

lemma primepow_cases:
  "primepow d \<longleftrightarrow>
     (  primepow_even d \<and> \<not> primepow_odd d \<and> \<not> prime d) \<or>
     (\<not> primepow_even d \<and>   primepow_odd d \<and> \<not> prime d) \<or>
     (\<not> primepow_even d \<and> \<not> primepow_odd d \<and>   prime d)"
  by sorry


subsection \<open>Deriving a recurrence for the psi function\<close>
  
lemma ln_fact_bounds:
  assumes "n > 0"
  shows "abs(ln (fact n) - n * ln n + n) \<le> 1 + ln n"
  by sorry

lemma ln_fact_diff_bounds:
  "abs(ln (fact n) - 2 * ln (fact (n div 2)) - n * ln 2) \<le> 4 * ln (if n = 0 then 1 else n) + 3"
  by sorry
  
lemma ln_primefact:
  assumes "n \<noteq> (0::nat)"
  shows   "ln n = (\<Sum>d=1..n. if primepow d \<and> d dvd n then ln (aprimedivisor d) else 0)" 
          (is "?lhs = ?rhs")
  by sorry

context
begin

private lemma divisors:
  fixes x d::nat
  assumes "x \<in> {1..n}"
  assumes "d dvd x"
  shows "\<exists>k\<in>{1..n div d}. x = d * k"
proof -
  from assms have "x \<le> n"
    by simp
  then have ub: "x div d \<le> n div d"
    by (simp add: div_le_mono \<open>x \<le> n\<close>)
  from assms have "1 \<le> x div d" by (auto elim!: dvdE)
  with ub have "x div d \<in> {1..n div d}"
    by simp
  with \<open>d dvd x\<close> show ?thesis by (auto intro!: bexI[of _ "x div d"])
qed

lemma ln_fact_conv_mangoldt: "ln (fact n) = (\<Sum>d=1..n. mangoldt d * floor (n / d))"
  by sorry

end

context
begin

private lemma div_2_mult_2_bds:
  fixes n d :: nat
  assumes "d > 0"
  shows "0 \<le> \<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor>" "\<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor> \<le> 1"
proof -
  have "\<lfloor>2::real\<rfloor> * \<lfloor>(n div 2) / d\<rfloor> \<le> \<lfloor>2 * ((n div 2) / d)\<rfloor>" 
    by (rule le_mult_floor) simp_all
  also from assms have "\<dots> \<le> \<lfloor>n / d\<rfloor>" by (intro floor_mono) (simp_all add: field_simps)
  finally show "0 \<le> \<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor>" by (simp add: algebra_simps)
next  
  have "real (n div d) \<le> real (2 * ((n div 2) div d) + 1)"
    by (subst div_mult2_eq [symmetric], simp only: mult.commute, subst div_mult2_eq) simp
  thus "\<lfloor>n / d\<rfloor> - 2 * \<lfloor>(n div 2) / d\<rfloor> \<le> 1"
    unfolding of_nat_add of_nat_mult floor_conv_div_nat [symmetric] by simp_all
qed

private lemma n_div_d_eq_1: "d \<in> {n div 2 + 1..n} \<Longrightarrow> \<lfloor>real n / real d\<rfloor> = 1"
  by (cases "n = d") (auto simp: field_simps intro: floor_eq)
    
lemma psi_bounds_ln_fact:
  shows "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n"
        "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
  by sorry

end

lemma psi_bounds_induct:
  "real n * ln 2 - (4 * ln (real (if n = 0 then 1 else n)) + 3) \<le> psi n"
  "psi n - psi (n div 2) \<le> real n * ln 2 + (4 * ln (real (if n = 0 then 1 else n)) + 3)"
  by sorry
  

subsection \<open>Bounding the psi function\<close>

text \<open>
  In this section, we will first prove the relatively tight estimate
  @{prop "psi n \<le> 3 / 2 + ln 2 * n"} for @{term "n \<le> 128"} and then use the 
  recurrence we have just derived to extend it to @{prop "psi n \<le> 551 / 256"} for 
  @{term "n \<le> 1024"}, at which point applying the recurrence can be used to prove 
  the same bound for arbitrarily big numbers.

  First of all, we will prove the bound for @{term "n <= 128"} using reflection and
  approximation.
\<close>  

context
begin

private lemma Ball_insertD:
  assumes "\<forall>x\<in>insert y A. P x"
  shows   "P y" "\<forall>x\<in>A. P x"
  using assms by auto

private lemma meta_eq_TrueE: "PROP A \<equiv> Trueprop True \<Longrightarrow> PROP A"
  by simp

private lemma pre_mangoldt_pos: "pre_mangoldt n > 0"
  unfolding pre_mangoldt_def by (auto simp: primepow_gt_Suc_0)

private lemma psi_conv_pre_mangoldt: "psi n = ln (real (prod pre_mangoldt {1..n}))"
  by (auto simp: psi_def mangoldt_def pre_mangoldt_def ln_prod primepow_gt_Suc_0 intro!: sum.cong)

private lemma eval_psi_aux1: "psi 0 = ln (real (numeral Num.One))"
  by (simp add: psi_def)

private lemma eval_psi_aux2:
  assumes "psi m = ln (real (numeral x))" "pre_mangoldt n = y" "m + 1 = n" "numeral x * y = z"
  shows   "psi n = ln (real z)"
proof -
  from assms(2) [symmetric] have [simp]: "y > 0" by (simp add: pre_mangoldt_pos)
  have "psi n = psi (Suc m)" by (simp add: assms(3) [symmetric])
  also have "\<dots> = ln (real y * (\<Prod>x = Suc 0..m. real (pre_mangoldt x)))"
    using assms(2,3) [symmetric] by (simp add: psi_conv_pre_mangoldt prod.nat_ivl_Suc' mult_ac)
  also have "\<dots> = ln (real y) + psi m"
    by (subst ln_mult) (simp_all add: pre_mangoldt_pos prod_pos psi_conv_pre_mangoldt)
  also have "psi m = ln (real (numeral x))" by fact
  also have "ln (real y) + \<dots> = ln (real (numeral x * y))" by (simp add: ln_mult)
  finally show ?thesis by (simp add: assms(4) [symmetric])
qed

private lemma Ball_atLeast0AtMost_doubleton:
  assumes "psi 0 \<le> 3 / 2 * ln 2 * real 0"
  assumes "psi 1 \<le> 3 / 2 * ln 2 * real 1"
  shows   "(\<forall>x\<in>{0..1}. psi x \<le> 3 / 2 * ln 2 * real x)"
  using assms unfolding One_nat_def atLeast0_atMost_Suc ball_simps by auto

private lemma Ball_atLeast0AtMost_insert:
  assumes "(\<forall>x\<in>{0..m}. psi x \<le> 3 / 2 * ln 2 * real x)"
  assumes "psi (numeral n) \<le> 3 / 2 * ln 2 * real (numeral n)" "m = pred_numeral n"
  shows   "(\<forall>x\<in>{0..numeral n}. psi x \<le> 3 / 2 * ln 2 * real x)"
  using assms
  by (subst numeral_eq_Suc[of n], subst atLeast0_atMost_Suc,
      subst ball_simps, simp only: numeral_eq_Suc [symmetric])

private lemma eval_psi_ineq_aux:
  assumes "psi n = x" "x \<le> 3 / 2 * ln 2 * n"
  shows   "psi n \<le> 3 / 2 * ln 2 * n"
  using assms by simp_all
    
private lemma eval_psi_ineq_aux2:
  assumes "numeral m ^ 2 \<le> (2::nat) ^ (3 * n)"
  shows   "ln (real (numeral m)) \<le> 3 / 2 * ln 2 * real n"
proof -
  have "ln (real (numeral m)) \<le> 3 / 2 * ln 2 * real n \<longleftrightarrow> 
          2 * log 2 (real (numeral m)) \<le> 3 * real n"
    by (simp add: field_simps log_def)
  also have "2 * log 2 (real (numeral m)) = log 2 (real (numeral m ^ 2))"
    by (subst of_nat_power, subst log_nat_power) simp_all
  also have "\<dots> \<le> 3 * real n \<longleftrightarrow> real ((numeral m) ^ 2) \<le> 2 powr real (3 * n)"
    by (subst Transcendental.log_le_iff) simp_all
  also have "2 powr (3 * n) = real (2 ^ (3 * n))" 
    by (simp add: powr_realpow [symmetric])
  also have "real ((numeral m) ^ 2) \<le> \<dots> \<longleftrightarrow> numeral m ^ 2 \<le> (2::nat) ^ (3 * n)"
    by (rule of_nat_le_iff)
  finally show ?thesis using assms by blast
qed

private lemma eval_psi_ineq_aux_mono:
  assumes "psi n = x" "psi m = x" "psi n \<le> 3 / 2 * ln 2 * n" "n \<le> m"
  shows   "psi m \<le> 3 / 2 * ln 2 * m"
proof -
  from assms have "psi m = psi n" by simp
  also have "\<dots> \<le> 3 / 2 * ln 2 * n" by fact
  also from \<open>n \<le> m\<close> have "\<dots> \<le> 3 / 2 * ln 2 * m" by simp
  finally show ?thesis .
qed

lemma not_primepow_1_nat: "\<not>primepow (1 :: nat)" by auto
                 
ML_file \<open>bertrand.ML\<close>

(* This should not take more than 1 minute *)
local_setup \<open>fn lthy =>
let
  fun tac ctxt =
    let
      val psi_cache = Bertrand.prove_psi ctxt 129
      fun prove_psi_ineqs ctxt =
        let
          fun tac goal_ctxt = 
            HEADGOAL (resolve_tac goal_ctxt @{thms eval_psi_ineq_aux2} THEN'
              Simplifier.simp_tac goal_ctxt)
          fun prove_by_approx n thm =
            let
              val thm = thm RS @{thm eval_psi_ineq_aux}
              val [prem] = Thm.prems_of thm
              val prem = Goal.prove ctxt [] [] prem (tac o #context)
            in
              prem RS thm
            end
          fun prove_by_mono last_thm last_thm' thm =
            let
              val thm = @{thm eval_psi_ineq_aux_mono} OF [last_thm, thm, last_thm']
              val [prem] = Thm.prems_of thm
              val prem =
                Goal.prove ctxt [] [] prem (fn {context = goal_ctxt, ...} =>
                  HEADGOAL (Simplifier.simp_tac goal_ctxt))
            in
              prem RS thm
            end
          fun go _ acc [] = acc
            | go last acc ((n, x, thm) :: xs) =
                let
                  val thm' =
                    case last of
                      NONE => prove_by_approx n thm
                    | SOME (last_x, last_thm, last_thm') => 
                        if last_x = x then 
                          prove_by_mono last_thm last_thm' thm 
                        else
                          prove_by_approx n thm
                in
                  go (SOME (x, thm, thm')) (thm' :: acc) xs
                end
        in
          rev o go NONE []
        end
            
      val psi_ineqs = prove_psi_ineqs ctxt psi_cache
      fun prove_ball ctxt (thm1 :: thm2 :: thms) =
            let
              val thm = @{thm Ball_atLeast0AtMost_doubleton} OF [thm1, thm2]
              fun solve_prem thm =
                let
                  val thm' =
                    Goal.prove ctxt [] [] (Thm.cprem_of thm 1 |> Thm.term_of)
                      (fn {context = goal_ctxt, ...} =>
                        HEADGOAL (Simplifier.simp_tac goal_ctxt))
                in
                  thm' RS thm
                end
              fun go thm thm' = (@{thm Ball_atLeast0AtMost_insert} OF [thm', thm]) |> solve_prem
            in
              fold go thms thm
            end
        | prove_ball _ _ = raise Match
    in
      HEADGOAL (resolve_tac ctxt [prove_ball ctxt psi_ineqs])
    end
  val thm = Goal.prove lthy [] [] @{prop "\<forall>n\<in>{0..128}. psi n \<le> 3 / 2 * ln 2 * n"} (tac o #context)
in
  Local_Theory.note ((@{binding psi_ubound_log_128}, []), [thm]) lthy |> snd
end
\<close>

end


context
begin
  
private lemma psi_ubound_aux:
  defines "f \<equiv> \<lambda>x::real. (4 * ln x + 3) / (ln 2 * x)"
  assumes "x \<ge> 2" "x \<le> y"
  shows   "f x \<ge> f y"
  by sorry

text \<open>
  These next rules are used in combination with @{thm psi_bounds_induct} and 
  @{thm psi_ubound_log_128} to extend the upper bound for @{term "psi"} from values no greater 
  than 128 to values no greater than 1024. The constant factor of the upper bound changes every 
  time, but once we have reached 1024, the recurrence is self-sustaining in the sense that we do 
  not have to adjust the constant factor anymore in order to double the range.
\<close>
lemma psi_ubound_log_double_cases':
  assumes "\<And>n. n \<le> m \<Longrightarrow> psi n \<le> c * ln 2 * real n" "n \<le> m'" "m' = 2*m"
          "c \<le> c'" "c \<ge> 0" "m \<ge> 1" "c' \<ge> 1 + c/2 + (4 * ln (m+1) + 3) / (ln 2 * (m+1))"
  shows   "psi n \<le> c' * ln 2 * real n"
  by sorry

end  

lemma psi_ubound_log_double_cases:
  assumes "\<forall>n\<le>m. psi n \<le> c * ln 2 * real n"
          "c' \<ge> 1 + c/2 + (4 * ln (m+1) + 3) / (ln 2 * (m+1))"
          "m' = 2*m" "c \<le> c'" "c \<ge> 0" "m \<ge> 1" 
  shows   "\<forall>n\<le>m'. psi n \<le> c' * ln 2 * real n"
  by sorry

lemma psi_ubound_log_1024:
  "\<forall>n\<le>1024. psi n \<le> 551 / 256 * ln 2 * real n"
  by sorry
  
lemma psi_bounds_sustained_induct:
  assumes "4 * ln (1 + 2 ^ j) + 3 \<le> d * ln 2 * (1 + 2^j)"
  assumes "4 / (1 + 2^j) \<le> d * ln 2"
  assumes "0 \<le> c"
  assumes "c / 2 + d + 1 \<le> c"
  assumes "j \<le> k"
  assumes "\<And>n. n \<le> 2^k \<Longrightarrow> psi n \<le> c * ln 2 * n"
  assumes "n \<le> 2^(Suc k)"
  shows "psi n \<le> c * ln 2 * n"
  by sorry

lemma psi_bounds_sustained:
  assumes "\<And>n. n \<le> 2^k \<Longrightarrow> psi n \<le> c * ln 2 * n"
  assumes "4 * ln (1 + 2^k) + 3 \<le> (c/2 - 1) * ln 2 * (1 + 2^k)"
  assumes "4 / (1 + 2^k) \<le> (c/2 - 1) * ln 2"
  assumes "c \<ge> 0"
  shows "psi n \<le> c * ln 2 * n"
  by sorry

lemma psi_ubound_log: "psi n \<le> 551 / 256 * ln 2 * n"
  by sorry

lemma psi_ubound_3_2: "psi n \<le> 3/2 * n"
  by sorry


subsection \<open>Doubling psi and theta\<close>  

lemma psi_residues_compare_2:
  "psi_odd_2 n \<le> psi_even_2 n"
  by sorry

lemma psi_residues_compare:
  "psi_odd n \<le> psi_even n"
  by sorry

lemma primepow_iff_even_sqr:
  "primepow n \<longleftrightarrow> primepow_even (n^2)"
  by sorry

lemma psi_sqrt: "psi (floor_sqrt n) = psi_even n"
  by sorry

lemma mangoldt_split:
  "mangoldt d = mangoldt_1 d + mangoldt_even d + mangoldt_odd d"
  by sorry

lemma psi_split: "psi n = theta n + psi_even n + psi_odd n"
  by sorry

lemma psi_mono: "m \<le> n \<Longrightarrow> psi m \<le> psi n" unfolding psi_def
  by sorry

lemma psi_pos: "0 \<le> psi n"
  by sorry

lemma mangoldt_odd_pos: "0 \<le> mangoldt_odd d"
  by sorry

lemma psi_odd_mono: "m \<le> n \<Longrightarrow> psi_odd m \<le> psi_odd n"
  by sorry

lemma psi_odd_pos: "0 \<le> psi_odd n"
  by sorry

lemma psi_theta:
  "theta n + psi (floor_sqrt n) \<le> psi n" "psi n \<le> theta n + 2 * psi (floor_sqrt n)"
  by sorry

context
begin

private lemma sum_minus_one: 
  "(\<Sum>x \<in> {1..y}. (- 1 :: real) ^ (x + 1)) = (if odd y then 1 else 0)"
  by (induction y) simp_all
  
private lemma div_invert:
  fixes x y n :: nat
  assumes "x > 0" "y > 0" "y \<le> n div x"
  shows "x \<le> n div y"
proof -
  from assms(1,3) have "y * x \<le> (n div x) * x"
    by simp
  also have "\<dots> \<le> n"
    by (simp add: minus_mod_eq_div_mult[symmetric])
  finally have "y * x \<le> n" .
  with assms(2) show ?thesis
    using div_le_mono[of "y*x" n y] by simp
qed

lemma sum_expand_lemma:
  "(\<Sum>d=1..n. (-1) ^ (d + 1) * psi (n div d)) = 
     (\<Sum>d = 1..n. (if odd (n div d) then 1 else 0) * mangoldt d)"
  by sorry

private lemma floor_half_interval:
  fixes n d :: nat
  assumes "d \<noteq> 0"
  shows "real (n div d) - real (2 * ((n div 2) div d)) = (if odd (n div d) then 1 else 0)"
proof -
  have "((n div 2) div d) = (n div (2 * d))"
    by (rule div_mult2_eq[symmetric])
  also have "\<dots> = ((n div d) div 2)"
    by (simp add: mult_ac div_mult2_eq)
  also have "real (n div d) - real (2 * \<dots>) = (if odd (n div d) then 1 else 0)"
    by (cases "odd (n div d)", cases "n div d = 0 ", simp_all)
  finally show ?thesis by simp
qed

lemma fact_expand_psi:
  "ln (fact n) - 2 * ln (fact (n div 2)) = (\<Sum>d=1..n. (-1)^(d+1) * psi (n div d))"
  by sorry
  
end

lemma psi_expansion_cutoff:
  assumes "m \<le> p"
  shows   "(\<Sum>d=1..2*m. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*p. (-1)^(d+1) * psi (n div d))"
          "(\<Sum>d=1..2*p+1. (-1)^(d+1) * psi (n div d)) \<le> (\<Sum>d=1..2*m+1. (-1)^(d+1) * psi (n div d))"
  by sorry

lemma fact_psi_bound_even:
  assumes "even k"
  shows   "(\<Sum>d=1..k. (-1)^(d+1) * psi (n div d)) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
  by sorry

lemma fact_psi_bound_odd:
  assumes "odd k"
  shows "ln (fact n) - 2 * ln (fact (n div 2)) \<le> (\<Sum>d=1..k. (-1)^(d+1) * psi (n div d))"
  by sorry

lemma fact_psi_bound_2_3:
  "psi n - psi (n div 2) \<le> ln (fact n) - 2 * ln (fact (n div 2))"
  "ln (fact n) - 2 * ln (fact (n div 2)) \<le> psi n - psi (n div 2) + psi (n div 3)"
  by sorry

lemma ub_ln_1200: "ln 1200 \<le> 57 / (8 :: real)"
  by sorry
  
lemma psi_double_lemma:
  assumes "n \<ge> 1200"
  shows "real n / 6 \<le> psi n - psi (n div 2)"
  by sorry

lemma theta_double_lemma:
  assumes "n \<ge> 1200"
  shows "theta (n div 2) < theta n"
  by sorry
  

subsection \<open>Proof of the main result\<close>

lemma theta_mono: "mono theta"
  by sorry
  
lemma theta_lessE:
  assumes "theta m < theta n" "m \<ge> 1"
  obtains p where "p \<in> {m<..n}" "prime p"
  by sorry

theorem bertrand:
  fixes   n :: nat
  assumes "n > 1"
  shows   "\<exists>p\<in>{n<..<2*n}. prime p"
  by sorry
  
  
subsection \<open>Proof of Mertens' first theorem\<close>

text \<open>
  The following proof of Mertens' first theorem was ported from John Harrison's HOL Light
  proof by Larry Paulson:
\<close>

lemma sum_integral_ubound_decreasing':
  fixes f :: "real \<Rightarrow> real"
  assumes "m \<le> n"
      and der: "\<And>x. x \<in> {of_nat m - 1..of_nat n} \<Longrightarrow> (g has_field_derivative f x) (at x)"
      and le:  "\<And>x y. \<lbrakk>real m - 1 \<le> x; x \<le> y; y \<le> real n\<rbrakk> \<Longrightarrow> f y \<le> f x"
    shows "(\<Sum>k = m..n. f (of_nat k)) \<le> g (of_nat n) - g (of_nat m - 1)"
  by sorry

lemma Mertens_lemma:
  assumes "n \<noteq> 0"
    shows "\<bar>(\<Sum>d = 1..n. mangoldt d / real d) - ln n\<bar> \<le> 4"
  by sorry

lemma Mertens_mangoldt_versus_ln:
  assumes "I \<subseteq> {1..n}"
  shows "\<bar>(\<Sum>i\<in>I. mangoldt i / i) - (\<Sum>p | prime p \<and> p \<in> I. ln p / p)\<bar> \<le> 3"
        (is "\<bar>?lhs\<bar> \<le> 3")
  by sorry

proposition Mertens:
  assumes "n \<noteq> 0"
  shows "\<bar>(\<Sum>p | prime p \<and> p \<le> n. ln p / of_nat p) - ln n\<bar> \<le> 7"
  by sorry

end
