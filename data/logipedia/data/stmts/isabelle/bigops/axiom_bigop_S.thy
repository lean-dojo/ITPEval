(*
  Statement-only formalization of Logipedia corpus artifact bigops.axiom_bigop_S:
  equality at successor indices between the abstract big-operation function and
  its body, uniformly over the result type. This file contains no proof.
*)

theory axiom_bigop_S
  imports Main
begin

consts
  bigop ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  bigop_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"

theorem axiom_bigop_S:
  "\<forall>n :: nat.
    (bigop (Suc n) ::
      (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a)
    = bigop_body (Suc n)"
  sorry

end
