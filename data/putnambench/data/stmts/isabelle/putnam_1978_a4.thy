theory putnam_1978_a4 imports Complex_Main
begin

definition putnam_1978_a4_bypass ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
"putnam_1978_a4_bypass \<equiv> \<lambda> S Smul.
  \<forall> a \<in> S. \<forall> b \<in> S. \<forall> c \<in> S. \<forall> d \<in> S.
    Smul (Smul a b) (Smul c d) = Smul a d"

theorem putnam_1978_a4:
  shows "(\<forall> (S :: 'a set) (Smul :: 'a \<Rightarrow> 'a \<Rightarrow> 'a).
        (((\<forall> a \<in> S. \<forall> b \<in> S. Smul a b \<in> S) \<and> putnam_1978_a4_bypass S Smul)
        \<longrightarrow> (\<forall> a \<in> S. \<forall> b \<in> S. \<forall> c \<in> S. Smul a b = c \<longrightarrow> (Smul c c = c \<and> (\<forall> d \<in> S. Smul a d = Smul c d))))) \<and>
        (\<exists> (S :: nat set) (Smul :: nat \<Rightarrow> nat \<Rightarrow> nat).
        (\<forall> a \<in> S. \<forall> b \<in> S. Smul a b \<in> S) \<and>
        putnam_1978_a4_bypass S Smul \<and> finite S \<and>
        (\<forall> a \<in> S. Smul a a = a) \<and>
        (\<exists> a \<in> S. \<exists> b \<in> S. Smul a b = a \<and> a \<noteq> b) \<and>
        (\<exists> a \<in> S. \<exists> b \<in> S. Smul a b \<noteq> a))"
  sorry

end
