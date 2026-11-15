(*
  Statement-only formalization of Logipedia corpus artifact bigops.let_clause_10471:
  a let-clause implication preserving filtered-product isomorphism premises and
  concluding the natural-number quotient-remainder decomposition. This file
  contains no proof.
*)

theory let_clause_10471
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

theorem let_clause_10471:
  "\<forall>n1 n2 :: nat.
    \<forall>p1 p2 :: nat \<Rightarrow> bool.
    \<forall>f1 f2 :: nat \<Rightarrow> nat.
    iso n1 n2 p1 p2 f1 f2 \<longrightarrow>
    (\<forall>h :: nat \<Rightarrow> nat.
      (\<exists>k :: nat \<Rightarrow> nat.
        ((\<forall>i. i < n1 \<longrightarrow> p1 i = True \<longrightarrow> f1 i = f2 (h i)) \<and>
          sub_hk h k n1 n2 p1 p2 f1 f2) \<and>
        sub_hk k h n2 n1 p2 p1 f2 f1) \<longrightarrow>
      (\<forall>k :: nat \<Rightarrow> nat.
        (((\<forall>i. i < n1 \<longrightarrow> p1 i = True \<longrightarrow> f1 i = f2 (h i)) \<and>
            sub_hk h k n1 n2 p1 p2 f1 f2) \<and>
          sub_hk k h n2 n1 p2 p1 f2 f1) \<longrightarrow>
        ((\<forall>i. i < n1 \<longrightarrow> p1 i = True \<longrightarrow> f1 i = f2 (h i)) \<and>
          sub_hk h k n1 n2 p1 p2 f1 f2) \<longrightarrow>
        (\<forall>i. i < n1 \<longrightarrow> p1 i = True \<longrightarrow> f1 i = f2 (h i)) \<longrightarrow>
        (\<forall>i m :: nat.
          (\<forall>f :: nat \<Rightarrow> bool.
            0 \<le> n1 \<longrightarrow>
            sub_hk h k 0 m p1 f f1 f2 \<longrightarrow>
            sub_hk k h m 0 f p1 f2 f1 \<longrightarrow>
            bigop 0 p1 1 (*) f1 = bigop m f 1 (*) f2) \<longrightarrow>
          (\<forall>p20 :: nat \<Rightarrow> bool.
            0 \<le> n1 \<longrightarrow>
            sub_hk h k 0 (Suc m) p1 p20 f1 f2 \<longrightarrow>
            sub_hk k h (Suc m) 0 p20 p1 f2 f1 \<longrightarrow>
            (\<forall>x2571 x2572 :: nat.
              x2571 =
                x2572 * (x2571 div x2572) + (x2571 mod x2572))))))"
  sorry

end
