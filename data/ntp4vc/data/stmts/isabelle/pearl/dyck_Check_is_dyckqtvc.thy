theory dyck_Check_is_dyckqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "./dyck_Dyck"
begin
definition fall :: "paren list \<Rightarrow> paren list \<Rightarrow> _"
  where "fall p s \<longleftrightarrow> dyck p \<and> (case s of Cons L _ \<Rightarrow> False | _ \<Rightarrow> True)" for p s
theorem is_dyck'vc:
  fixes w :: "paren list"
  fixes o2 :: "paren list"
  shows "\<forall>(o1 :: paren list). w = o2 @ o1 \<and> fall o2 o1 \<and> (\<forall>(p2 :: paren list) (s :: paren list). w = p2 @ s \<and> fall p2 s \<longrightarrow> p2 = o2 \<and> s = o1) \<longrightarrow> (\<forall>(result :: bool). (case o1 of Nil \<Rightarrow> result = True | _ \<Rightarrow> result = False) \<longrightarrow> result = True \<longleftrightarrow> dyck w)"
  and "(\<forall>(p :: paren list) (s :: paren list). w = p @ s \<longrightarrow> \<not>fall p s) \<longrightarrow> \<not>dyck w"
  sorry
end
