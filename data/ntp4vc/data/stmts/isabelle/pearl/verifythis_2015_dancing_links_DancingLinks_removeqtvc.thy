theory verifythis_2015_dancing_links_DancingLinks_removeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  dll
consts prev :: "dll \<Rightarrow> int list"
consts "next" :: "dll \<Rightarrow> int list"
consts n :: "dll \<Rightarrow> int"
axiomatization where dll'invariant'0:   "length (prev self) = length (next self)"
  for self :: "dll"
axiomatization where dll'invariant'1:   "int (length (next self)) = n self"
  for self :: "dll"
definition dll'eq :: "dll \<Rightarrow> dll \<Rightarrow> _"
  where "dll'eq a b \<longleftrightarrow> prev a = prev b \<and> next a = next b \<and> n a = n b" for a b
axiomatization where dll'inj:   "a = b"
 if "dll'eq a b"
  for a :: "dll"
  and b :: "dll"
definition valid_in :: "dll \<Rightarrow> int \<Rightarrow> _"
  where "valid_in l i \<longleftrightarrow> ((0 :: int) \<le> i \<and> i < n l) \<and> ((0 :: int) \<le> prev l ! nat i \<and> prev l ! nat i < n l) \<and> ((0 :: int) \<le> next l ! nat i \<and> next l ! nat i < n l) \<and> next l ! nat (prev l ! nat i) = i \<and> prev l ! nat (next l ! nat i) = i" for l i
definition valid_out :: "dll \<Rightarrow> int \<Rightarrow> _"
  where "valid_out l i \<longleftrightarrow> ((0 :: int) \<le> i \<and> i < n l) \<and> ((0 :: int) \<le> prev l ! nat i \<and> prev l ! nat i < n l) \<and> ((0 :: int) \<le> next l ! nat i \<and> next l ! nat i < n l) \<and> next l ! nat (prev l ! nat i) = next l ! nat i \<and> prev l ! nat (next l ! nat i) = prev l ! nat i" for l i
definition is_list :: "dll \<Rightarrow> int list \<Rightarrow> _"
  where "is_list l s \<longleftrightarrow> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length s) \<longrightarrow> ((0 :: int) \<le> s ! nat k \<and> s ! nat k < n l) \<and> prev l ! nat (s ! nat k) = s ! nat (if k = (0 :: int) then int (length s) - (1 :: int) else k - (1 :: int)) \<and> next l ! nat (s ! nat k) = s ! nat (if k = int (length s) - (1 :: int) then 0 :: int else k + (1 :: int)) \<and> (\<forall>(k' :: int). (0 :: int) \<le> k' \<and> k' < int (length s) \<longrightarrow> \<not>k = k' \<longrightarrow> \<not>s ! nat k = s ! nat k'))" for l s
theorem remove'vc:
  fixes l :: "dll"
  fixes i :: "int"
  fixes s :: "int list"
  assumes fact0: "valid_in l i"
  assumes fact1: "is_list l (Cons i s)"
  shows "let o1 :: int list = prev l in ((0 :: int) \<le> i \<and> i < int (length o1)) \<and> (let o2 :: int = o1 ! nat i; o3 :: int list = next l in ((0 :: int) \<le> i \<and> i < int (length o3)) \<and> (let o4 :: int = o3 ! nat i; o5 :: int list = prev l in ((0 :: int) \<le> o4 \<and> o4 < int (length o5)) \<and> (length (o5[nat o4 := o2]) = length o5 \<longrightarrow> length (o5[nat o4 := o2]) = length (prev l) \<longrightarrow> nth (o5[nat o4 := o2]) o nat = (nth o5 o nat)(o4 := o2) \<longrightarrow> ((0 :: int) \<le> i \<and> i < int (length (next l))) \<and> (let o6 :: int = next l ! nat i in ((0 :: int) \<le> i \<and> i < int (length (o5[nat o4 := o2]))) \<and> (let o7 :: int = o5[nat o4 := o2] ! nat i in ((0 :: int) \<le> o7 \<and> o7 < int (length (next l))) \<and> (\<forall>(l1 :: dll). length ((next l)[nat o7 := o6]) = length (next l) \<longrightarrow> length ((next l)[nat o7 := o6]) = length (next l) \<longrightarrow> nth ((next l)[nat o7 := o6]) o nat = (nth (next l) o nat)(o7 := o6) \<longrightarrow> (length (o5[nat o4 := o2]) = length ((next l)[nat o7 := o6]) \<and> int (length ((next l)[nat o7 := o6])) = n l) \<and> (n l = n l1 \<and> (next l)[nat o7 := o6] = next l1 \<and> o5[nat o4 := o2] = prev l1 \<longrightarrow> valid_out l1 i \<and> is_list l1 s)))))))"
  sorry
end
