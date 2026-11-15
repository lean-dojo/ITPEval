(*
  Statement-only formalization of Logipedia corpus artifact bigops.eq_bigop_body_S:
  Leibniz equality at a successor index between the abstract big-operation body
  and the function that conditionally combines the current value with the
  preceding big operation. This file contains no proof.
*)

theory eq_bigop_body_S
  imports Main
begin

consts
  bigop ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  bigop_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"

theorem eq_bigop_body_S:
  "\<forall>n :: nat.
    (bigop_body (Suc n) ::
      (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a)
    = (\<lambda>p nil op f.
        if p n
        then op (f n) (bigop n p nil op f)
        else bigop n p nil op f)"
  sorry

end
