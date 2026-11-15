(*
  Statement-only formalization of Logipedia corpus artifact bigops.bigop_Sfalse:
  a Boolean-filtered polymorphic big operation is unchanged at a successor
  index when the predicate is false there. This file contains no proof.
*)

theory bigop_Sfalse
  imports Main
begin

fun bigop ::
  "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
    ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "bigop 0 p nil op f = nil"
| "bigop (Suc n) p nil op f =
    (if p n
     then op (f n) (bigop n p nil op f)
     else bigop n p nil op f)"

theorem bigop_Sfalse:
  fixes k :: nat
    and p :: "nat \<Rightarrow> bool"
    and nil :: 'a
    and op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and f :: "nat \<Rightarrow> 'a"
  assumes "p k = False"
  shows "bigop (Suc k) p nil op f = bigop k p nil op f"
  sorry

end
