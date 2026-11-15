(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_11,
  catalog title "findMajorityElement": an executable list program returns the
  first integer occurring strictly more than half the list length, or returns
  -1 when no such integer exists, together with its correctness contract. This
  file contains no proof.
*)

theory verina_advanced_11
  imports Main
begin

definition countOccurrences :: "int \<Rightarrow> int list \<Rightarrow> nat" where
  "countOccurrences n lst =
    foldl (\<lambda>acc x. if x = n then acc + 1 else acc) 0 lst"

definition findMajorityElement_precond :: "int list \<Rightarrow> bool" where
  "findMajorityElement_precond lst \<longleftrightarrow> True"

fun findMajorityCandidate :: "int list \<Rightarrow> int list \<Rightarrow> int option" where
  "findMajorityCandidate original [] = None"
| "findMajorityCandidate original (x # xs) =
    (if countOccurrences x original > length original div 2
     then Some x
     else findMajorityCandidate original xs)"

definition findMajorityElement :: "int list \<Rightarrow> int" where
  "findMajorityElement lst =
    (case findMajorityCandidate lst lst of
       Some x \<Rightarrow> x
     | None \<Rightarrow> -1)"

definition findMajorityElement_postcond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "findMajorityElement_postcond lst result \<longleftrightarrow>
    (let count = (\<lambda>x. length (filter (\<lambda>y. y = x) lst));
         n = length lst;
         majority =
           (count result > n div 2 \<and>
            list_all (\<lambda>x. count x \<le> n div 2 \<or> x = result) lst)
     in (result = -1 \<longrightarrow>
           list_all (\<lambda>x. count x \<le> n div 2) lst \<or> majority) \<and>
        (result \<noteq> -1 \<longrightarrow> majority))"

theorem findMajorityElement_spec_satisfied:
  assumes "findMajorityElement_precond lst"
  shows "findMajorityElement_postcond lst (findMajorityElement lst)"
  sorry

end
