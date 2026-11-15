(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.congruent_pi, catalog title fermat.congruent_pi: for every
  natural-valued function and positive natural modulus, the product of its
  first n values is congruent modulo that modulus to the product of their
  remainders. This file contains no proof.
*)

theory congruent_pi
  imports Main
begin

fun bigop ::
  "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
    ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "bigop 0 predicate identity operation f = identity"
| "bigop (Suc n) predicate identity operation f =
    (if predicate n
     then operation (f n) (bigop n predicate identity operation f)
     else bigop n predicate identity operation f)"

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent x y p \<longleftrightarrow> x mod p = y mod p"

theorem congruent_pi:
  fixes f :: "nat \<Rightarrow> nat"
    and n p :: nat
  assumes "0 < p"
  shows "congruent
    (bigop n (\<lambda>i. True) 1 (\<lambda>x y. x * y) (\<lambda>i. f i))
    (bigop n (\<lambda>i. True) 1 (\<lambda>x y. x * y) (\<lambda>i. f i mod p))
    p"
  sorry

end
