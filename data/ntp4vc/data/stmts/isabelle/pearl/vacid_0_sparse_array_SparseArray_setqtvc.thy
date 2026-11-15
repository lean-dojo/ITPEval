theory vacid_0_sparse_array_SparseArray_setqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_MapInjection"
begin
typedecl 'a sparse_array
consts "values" :: "'a sparse_array \<Rightarrow> 'a list"
consts index :: "'a sparse_array \<Rightarrow> int list"
consts "back" :: "'a sparse_array \<Rightarrow> int list"
consts card :: "'a sparse_array \<Rightarrow> int"
consts def1 :: "'a sparse_array \<Rightarrow> 'a"
axiomatization where sparse_array'invariant'0:   "(0 :: int) \<le> card self"
  for self :: "'a sparse_array"
axiomatization where sparse_array'invariant'1:   "card self \<le> int (length (values self))"
  for self :: "'a sparse_array"
axiomatization where sparse_array'invariant'2:   "int (length (values self)) \<le> (1000 :: int)"
  for self :: "'a sparse_array"
axiomatization where sparse_array'invariant'3:   "length (values self) = length (index self)"
  for self :: "'a sparse_array"
axiomatization where sparse_array'invariant'4:   "length (index self) = length (back self)"
  for self :: "'a sparse_array"
axiomatization where sparse_array'invariant'5:   "\<forall>(i :: int). (0 :: int) \<le> i \<and> i < card self \<longrightarrow> ((0 :: int) \<le> back self ! nat i \<and> back self ! nat i < int (length (values self))) \<and> index self ! nat (back self ! nat i) = i"
  for self :: "'a sparse_array"
definition sparse_array'eq :: "'a sparse_array \<Rightarrow> 'a sparse_array \<Rightarrow> _"
  where "sparse_array'eq a b \<longleftrightarrow> values a = values b \<and> index a = index b \<and> back a = back b \<and> card a = card b \<and> def1 a = def1 b" for a b
axiomatization where sparse_array'inj:   "a = b"
 if "sparse_array'eq a b"
  for a :: "'a sparse_array"
  and b :: "'a sparse_array"
definition is_elt :: "'a sparse_array \<Rightarrow> int \<Rightarrow> _"
  where "is_elt a i \<longleftrightarrow> ((0 :: int) \<le> index a ! nat i \<and> index a ! nat i < card a) \<and> back a ! nat (index a ! nat i) = i" for a i
definition "value" :: "'a sparse_array \<Rightarrow> int \<Rightarrow> 'a"
  where "value a i = (if is_elt a i then values a ! nat i else def1 a)" for a i
definition length :: "'a sparse_array \<Rightarrow> int"
  where "length a = int (List.length (values a))" for a
theorem set'vc:
  fixes i :: "int"
  fixes a :: "'a sparse_array"
  fixes v :: "'a"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < length a"
  shows "let o1 :: 'a list = values a in ((0 :: int) \<le> i \<and> i < int (List.length o1)) \<and> (\<forall>(a1 :: 'a sparse_array). List.length (o1[nat i := v]) = List.length o1 \<longrightarrow> List.length (o1[nat i := v]) = List.length (values a) \<longrightarrow> nth (o1[nat i := v]) o nat = (nth o1 o nat)(i := v) \<longrightarrow> (((0 :: int) \<le> card a \<and> card a \<le> int (List.length (o1[nat i := v])) \<and> int (List.length (o1[nat i := v])) \<le> (1000 :: int)) \<and> (List.length (o1[nat i := v]) = List.length (index a) \<and> List.length (index a) = List.length (back a)) \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < card a \<longrightarrow> ((0 :: int) \<le> back a ! nat i1 \<and> back a ! nat i1 < int (List.length (o1[nat i := v]))) \<and> index a ! nat (back a ! nat i1) = i1)) \<and> (def1 a = def1 a1 \<and> card a = card a1 \<and> back a = back a1 \<and> index a = index a1 \<and> o1[nat i := v] = values a1 \<longrightarrow> ((0 :: int) \<le> i \<and> i < length a1) \<and> (if \<not>is_elt a1 i then let o2 :: int = card a1; o3 :: int list = index a1 in ((0 :: int) \<le> i \<and> i < int (List.length o3)) \<and> (List.length (o3[nat i := o2]) = List.length o3 \<longrightarrow> List.length (o3[nat i := o2]) = List.length (index a1) \<longrightarrow> nth (o3[nat i := o2]) o nat = (nth o3 o nat)(i := o2) \<longrightarrow> ((0 :: int) \<le> card a1 \<and> card a1 < int (List.length (back a1))) \<and> (List.length ((back a1)[nat (card a1) := i]) = List.length (back a1) \<longrightarrow> List.length ((back a1)[nat (card a1) := i]) = List.length (back a1) \<longrightarrow> nth ((back a1)[nat (card a1) := i]) o nat = (nth (back a1) o nat)(card a1 := i) \<longrightarrow> (\<forall>(a2 :: 'a sparse_array). (((0 :: int) \<le> card a1 + (1 :: int) \<and> card a1 + (1 :: int) \<le> int (List.length (values a1)) \<and> int (List.length (values a1)) \<le> (1000 :: int)) \<and> (List.length (values a1) = List.length (o3[nat i := o2]) \<and> List.length (o3[nat i := o2]) = List.length ((back a1)[nat (card a1) := i])) \<and> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < card a1 + (1 :: int) \<longrightarrow> ((0 :: int) \<le> (back a1)[nat (card a1) := i] ! nat i1 \<and> (back a1)[nat (card a1) := i] ! nat i1 < int (List.length (values a1))) \<and> o3[nat i := o2] ! nat ((back a1)[nat (card a1) := i] ! nat i1) = i1)) \<and> (def1 a1 = def1 a2 \<and> card a1 + (1 :: int) = card a2 \<and> (back a1)[nat (card a1) := i] = back a2 \<and> o3[nat i := o2] = index a2 \<and> values a1 = values a2 \<longrightarrow> value a2 i = v \<and> (\<forall>(j :: int). \<not>j = i \<longrightarrow> value a2 j = value a j))))) else value a1 i = v \<and> (\<forall>(j :: int). \<not>j = i \<longrightarrow> value a1 j = value a j))))"
  sorry
end
