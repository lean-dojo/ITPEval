theory Hello
  imports Main
begin

lemma itpeval_target: "P \<Longrightarrow> P \<and> P"
  apply (rule conjI)
  apply (assumption)
  apply (assumption)
  done

end
