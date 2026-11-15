(*
  Statement-only formalization of VERINA corpus artifact verina_basic_79
  (verina__isabelle__verina_basic_79), catalog title "onlineMax": an
  executable scan computes the maximum of the first x integer-array entries
  and then returns the first later index whose value exceeds that maximum, or
  the final array index if none does, together with its precondition,
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_79
  imports Main
begin

definition onlineMax_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "onlineMax_getBang a i =
    (if i < length a then a ! i else 0)"

definition onlineMax_precond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "onlineMax_precond a x \<longleftrightarrow>
    length a > 0 \<and> x > 0 \<and> x < length a"

definition findBest_step ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "findBest_step a best i =
    (let candidate = onlineMax_getBang a i
     in if candidate > best then candidate else best)"

definition findBest ::
    "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "findBest a x i best =
    foldl (findBest_step a) best [i..<x]"

fun findP_scan ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "findP_scan [] m i fallback = fallback"
| "findP_scan (y # ys) m i fallback =
    (if y > m then i else findP_scan ys m (i + 1) fallback)"

definition findP ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "findP a x m i =
    findP_scan (drop i a) m i (length a - 1)"

definition onlineMax ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<times> nat" where
  "onlineMax a x =
    (let best = onlineMax_getBang a 0;
         m = findBest a x 1 best;
         p = findP a x m x
     in (m, p))"

definition onlineMax_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> (int \<times> nat) \<Rightarrow> bool" where
  "onlineMax_postcond a x result \<longleftrightarrow>
    (let m = fst result;
         p = snd result
     in (x \<le> p \<and> p < length a) \<and>
        (\<forall>i. i < x \<longrightarrow> onlineMax_getBang a i \<le> m) \<and>
        (\<exists>i. i < x \<and> onlineMax_getBang a i = m) \<and>
        (\<forall>i. x \<le> i \<longrightarrow> i < p \<longrightarrow>
          onlineMax_getBang a i \<le> m) \<and>
        (onlineMax_getBang a p > m \<or>
          (p = length a - 1 \<and>
           (\<forall>i. x \<le> i \<longrightarrow> i < length a \<longrightarrow>
             onlineMax_getBang a i \<le> m))))"

theorem onlineMax_spec_satisfied:
  fixes a :: "int list"
    and x :: nat
  assumes "onlineMax_precond a x"
  shows "onlineMax_postcond a x (onlineMax a x)"
  sorry

end
