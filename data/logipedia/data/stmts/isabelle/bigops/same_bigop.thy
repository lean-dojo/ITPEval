(*
  Statement-only formalization of Logipedia corpus artifact bigops.same_bigop:
  equality of two Boolean-filtered polymorphic big operations when their filters
  agree below the bound and their selected values agree. This file contains no proof.
*)

theory same_bigop
  imports Main
begin

definition sameF_upto ::
  "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "sameF_upto k f g \<longleftrightarrow>
    (\<forall>i. i < k \<longrightarrow> f i = g i)"

definition sameF_p ::
  "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow>
    (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "sameF_p k p f g \<longleftrightarrow>
    (\<forall>i. i < k \<longrightarrow> p i = True \<longrightarrow> f i = g i)"

fun bigop ::
  "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
    ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "bigop 0 p nil op f = nil"
| "bigop (Suc n) p nil op f =
    (if p n
     then op (f n) (bigop n p nil op f)
     else bigop n p nil op f)"

theorem same_bigop:
  fixes k :: nat
    and p1 p2 :: "nat \<Rightarrow> bool"
    and nil :: 'a
    and op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and f g :: "nat \<Rightarrow> 'a"
  assumes "sameF_upto k p1 p2"
    and "sameF_p k p1 f g"
  shows "bigop k p1 nil op f = bigop k p2 nil op g"
  sorry

end
