(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.eq_fact_pi_p, catalog title fermat.eq_fact_pi_p: every natural
  number's factorial equals the product of the first n positive natural
  numbers. This file contains no proof.
*)

theory eq_fact_pi_p
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

theorem eq_fact_pi_p:
  "\<forall>n :: nat.
    fact n =
      bigop (Suc n - Suc 0)
        (\<lambda>i. True)
        (Suc 0)
        (*)
        (\<lambda>i. i + Suc 0)"
  sorry

end
