theory lattice_like
  imports Main
begin

locale lattice_like =
  fixes le  :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<preceq>" 50)
    and inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<sqinter>" 60)
    and sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<squnion>" 65)
  assumes le_refl   : "\<And>x. x \<preceq> x"
    and   le_trans  : "\<And>x y z. x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
    and   le_antisym: "\<And>x y. x \<preceq> y \<Longrightarrow> y \<preceq> x \<Longrightarrow> x = y"
    and   le_inf_left  : "\<And>a b. inf a b \<preceq> a"
    and   le_inf_right : "\<And>a b. inf a b \<preceq> b"
    and   le_inf_intro : "\<And>c a b. c \<preceq> a \<Longrightarrow> c \<preceq> b \<Longrightarrow> c \<preceq> inf a b"
    and   le_sup_left  : "\<And>a b. a \<preceq> sup a b"
    and   le_sup_right : "\<And>a b. b \<preceq> sup a b"
    and   sup_le_intro : "\<And>a b c. a \<preceq> c \<Longrightarrow> b \<preceq> c \<Longrightarrow> sup a b \<preceq> c"
begin

lemma inf_comm: "a \<sqinter> b = b \<sqinter> a"
  sorry
lemma sup_comm: "a \<squnion> b = b \<squnion> a"
  sorry
lemma inf_assoc: "(a \<sqinter> b) \<sqinter> c = a \<sqinter> (b \<sqinter> c)"
  sorry
lemma sup_assoc: "(a \<squnion> b) \<squnion> c = a \<squnion> (b \<squnion> c)"
  sorry
lemma inf_absorption: "a \<sqinter> (a \<squnion> b) = a"
  sorry
lemma sup_absorption: "a \<squnion> (a \<sqinter> b) = a"
  sorry
end

end
