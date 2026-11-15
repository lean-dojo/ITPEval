(*
  Statement-only formalization of thousand-theorems corpus artifact Q7888360
  (thousand-theorems__isabelle__Q7888360), "Structure theorem for finitely
  generated modules over a principal ideal domain": every finitely generated
  module over a PID is linearly equivalent to a finite free module times a
  finite direct sum of cyclic prime-power quotient modules. This file contains
  no proof.
*)

theory Q7888360_structure_theorem_for_finitely_generated_modules_over_a_prin
  imports Main
begin

definition q7888360_irreducible :: "'r::idom \<Rightarrow> bool" where
  "q7888360_irreducible p \<longleftrightarrow>
    p \<noteq> 0 \<and>
    \<not> p dvd 1 \<and>
    (\<forall>a b. p = a * b \<longrightarrow> a dvd 1 \<or> b dvd 1)"

definition q7888360_ideal :: "'r::comm_ring_1 set \<Rightarrow> bool" where
  "q7888360_ideal I \<longleftrightarrow>
    0 \<in> I \<and>
    (\<forall>x \<in> I. -x \<in> I) \<and>
    (\<forall>x \<in> I. \<forall>y \<in> I. x + y \<in> I) \<and>
    (\<forall>a. \<forall>x \<in> I. a * x \<in> I)"

definition q7888360_principal_ideal :: "'r::comm_ring_1 \<Rightarrow> 'r set" where
  "q7888360_principal_ideal a = {x. \<exists>r. x = r * a}"

definition q7888360_pid :: "'r::idom itself \<Rightarrow> bool" where
  "q7888360_pid TYPE('r) \<longleftrightarrow>
    (\<forall>I :: 'r set. q7888360_ideal I \<longrightarrow>
      (\<exists>a. I = q7888360_principal_ideal a))"

definition q7888360_module ::
    "('r::idom \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q7888360_module scale \<longleftrightarrow>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>x. scale 0 x = 0) \<and>
    (\<forall>a. scale a 0 = 0)"

fun q7888360_linear_combination ::
    "('r::idom \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow>
      ('r \<times> 'm) list \<Rightarrow> 'm" where
  "q7888360_linear_combination scale [] = 0"
| "q7888360_linear_combination scale ((a, x) # xs) =
    scale a x + q7888360_linear_combination scale xs"

definition q7888360_finitely_generated ::
    "('r::idom \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q7888360_finitely_generated scale \<longleftrightarrow>
    (\<exists>G :: 'm set. finite G \<and>
      (\<forall>x. \<exists>xs :: ('r \<times> 'm) list.
        set (map snd xs) \<subseteq> G \<and>
        q7888360_linear_combination scale xs = x))"

definition q7888360_coset ::
    "'r::idom \<Rightarrow> 'r \<Rightarrow> 'r set" where
  "q7888360_coset g x =
    {y. \<exists>z \<in> q7888360_principal_ideal g. y = x + z}"

definition q7888360_quotient_carrier ::
    "'r::idom \<Rightarrow> 'r set set" where
  "q7888360_quotient_carrier g = q7888360_coset g ` UNIV"

definition q7888360_quotient_add ::
    "'r::idom set \<Rightarrow> 'r set \<Rightarrow> 'r set" where
  "q7888360_quotient_add A B =
    {z. \<exists>x \<in> A. \<exists>y \<in> B. z = x + y}"

definition q7888360_quotient_scale ::
    "'r::idom \<Rightarrow> 'r \<Rightarrow> 'r set \<Rightarrow> 'r set" where
  "q7888360_quotient_scale g a A =
    {y. \<exists>x \<in> A. \<exists>z \<in> q7888360_principal_ideal g.
      y = a * x + z}"

definition q7888360_free_carrier :: "nat \<Rightarrow> 'r list set" where
  "q7888360_free_carrier n = {xs. length xs = n}"

definition q7888360_torsion_carrier ::
    "'r::idom list \<Rightarrow> nat list \<Rightarrow> 'r set list set" where
  "q7888360_torsion_carrier ps es =
    {qs. length es = length ps \<and>
      length qs = length ps \<and>
      (\<forall>i<length ps.
        qs ! i \<in> q7888360_quotient_carrier ((ps ! i) ^ (es ! i)))}"

definition q7888360_target_carrier ::
    "nat \<Rightarrow> 'r::idom list \<Rightarrow> nat list \<Rightarrow>
      ('r list \<times> 'r set list) set" where
  "q7888360_target_carrier n ps es =
    q7888360_free_carrier n \<times> q7888360_torsion_carrier ps es"

definition q7888360_target_add ::
    "nat \<Rightarrow> 'r::idom list \<Rightarrow>
      ('r list \<times> 'r set list) \<Rightarrow>
      ('r list \<times> 'r set list) \<Rightarrow>
      ('r list \<times> 'r set list)" where
  "q7888360_target_add n ps x y =
    (map (\<lambda>i. fst x ! i + fst y ! i) [0..<n],
      map (\<lambda>i. q7888360_quotient_add (snd x ! i) (snd y ! i))
        [0..<length ps])"

definition q7888360_target_scale ::
    "nat \<Rightarrow> 'r::idom list \<Rightarrow> nat list \<Rightarrow> 'r \<Rightarrow>
      ('r list \<times> 'r set list) \<Rightarrow>
      ('r list \<times> 'r set list)" where
  "q7888360_target_scale n ps es a x =
    (map (\<lambda>i. a * (fst x ! i)) [0..<n],
      map (\<lambda>i.
        q7888360_quotient_scale ((ps ! i) ^ (es ! i)) a (snd x ! i))
        [0..<length ps])"

definition q7888360_linear_equiv ::
    "('r::idom \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm) \<Rightarrow>
      nat \<Rightarrow> 'r list \<Rightarrow> nat list \<Rightarrow>
      ('m \<Rightarrow> ('r list \<times> 'r set list)) \<Rightarrow> bool" where
  "q7888360_linear_equiv scale n ps es f \<longleftrightarrow>
    bij_betw f UNIV (q7888360_target_carrier n ps es) \<and>
    (\<forall>x y.
      f (x + y) = q7888360_target_add n ps (f x) (f y)) \<and>
    (\<forall>a x.
      f (scale a x) = q7888360_target_scale n ps es a (f x))"

theorem q7888360_structure_theorem:
  fixes scale :: "'r::idom \<Rightarrow> 'm::ab_group_add \<Rightarrow> 'm"
  assumes "q7888360_pid TYPE('r)"
    and "q7888360_module scale"
    and "q7888360_finitely_generated scale"
  shows "\<exists>n ps es f.
    length es = length ps \<and>
    (\<forall>p \<in> set ps. q7888360_irreducible p) \<and>
    q7888360_linear_equiv scale n ps es f"
  sorry

end
