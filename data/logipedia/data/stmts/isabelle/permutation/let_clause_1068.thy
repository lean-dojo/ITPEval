(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.let_clause_1068, catalog title "permutation.let_clause_1068":
  under the source's explicit bounded permutation, range, injectivity, and
  equality hypotheses, a natural-number input has its specified image.
  This file contains no proof.
*)

theory let_clause_1068
  imports Main
begin

definition logipedia_injn :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_injn f n \<longleftrightarrow>
    (\<forall>i j :: nat.
      i \<le> n \<longrightarrow> j \<le> n \<longrightarrow>
      f i = f j \<longrightarrow> i = j)"

definition logipedia_permut :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_permut f n \<longleftrightarrow>
    (\<forall>i :: nat. i \<le> n \<longrightarrow> f i \<le> n) \<and>
    logipedia_injn f n"

theorem let_clause_1068:
  "\<forall>f :: nat \<Rightarrow> nat.
    \<forall>n :: nat.
      logipedia_permut f n \<longrightarrow>
      (\<forall>i j :: nat.
        i \<le> n \<longrightarrow>
        j \<le> n \<longrightarrow>
        (\<forall>a :: nat.
          (a \<le> n \<and> f a = i) \<longrightarrow>
          a \<le> n \<longrightarrow>
          f a = i \<longrightarrow>
          (\<forall>b :: nat.
            (b \<le> n \<and> f b = j) \<longrightarrow>
            b \<le> n \<longrightarrow>
            f b = j \<longrightarrow>
            (\<forall>i0 :: nat. i0 \<le> n \<longrightarrow> f i0 \<le> n) \<longrightarrow>
            logipedia_injn f n \<longrightarrow>
            a = b \<longrightarrow>
            f a = i)))"
  sorry

end
