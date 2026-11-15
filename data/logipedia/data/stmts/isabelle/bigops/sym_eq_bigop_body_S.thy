(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sym_eq_bigop_body_S: Leibniz equality at a successor index from the
  function that conditionally combines the current value with the preceding
  big operation to the abstract big-operation body. This file contains no proof.
*)

theory sym_eq_bigop_body_S
  imports Main
begin

consts
  bigop ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  bigop_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"

theorem sym_eq_bigop_body_S:
  "\<forall>n :: nat.
    (\<lambda>p nil op f.
      if p n
      then op (f n) (bigop n p nil op f)
      else bigop n p nil op f)
    = (bigop_body (Suc n) ::
      (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a)"
  sorry

end
