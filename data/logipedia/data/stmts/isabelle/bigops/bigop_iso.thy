(*
  Statement-only formalization of Logipedia corpus artifact bigops.bigop_iso:
  invariance of a Boolean-filtered natural-number product under a value-preserving
  bijection between its selected prefix indices. This file contains no proof.
*)

theory bigop_iso
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

definition sub_hk ::
  "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow>
    (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
where
  "sub_hk h k n1 n2 p1 p2 f1 f2 \<longleftrightarrow>
    (\<forall>i. i < n1 \<longrightarrow> p1 i = True \<longrightarrow>
      (h i < n2 \<and> p2 (h i) = True) \<and> k (h i) = i)"

definition iso ::
  "nat \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow>
    (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
where
  "iso n1 n2 p1 p2 f1 f2 \<longleftrightarrow>
    (\<exists>h k :: nat \<Rightarrow> nat.
      ((\<forall>i. i < n1 \<longrightarrow> p1 i = True \<longrightarrow> f1 i = f2 (h i)) \<and>
        sub_hk h k n1 n2 p1 p2 f1 f2) \<and>
      sub_hk k h n2 n1 p2 p1 f2 f1)"

theorem bigop_iso:
  fixes n1 n2 :: nat
    and p1 p2 :: "nat \<Rightarrow> bool"
    and f1 f2 :: "nat \<Rightarrow> nat"
  assumes "iso n1 n2 p1 p2 f1 f2"
  shows "bigop n1 p1 1 (*) f1 = bigop n2 p2 1 (*) f2"
  oops

end
