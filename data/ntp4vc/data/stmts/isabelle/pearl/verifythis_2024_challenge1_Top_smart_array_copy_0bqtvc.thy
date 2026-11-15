theory verifythis_2024_challenge1_Top_smart_array_copy_0bqtvc
  imports "NTP4Verif.NTP4Verif"
begin
definition permutation :: "int \<Rightarrow> int list \<Rightarrow> _"
  where "permutation l p \<longleftrightarrow> ((0 :: int) \<le> l \<and> l \<le> int (length p)) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < l \<longrightarrow> (0 :: int) \<le> p ! nat i \<and> p ! nat i < l) \<and> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < l \<longrightarrow> (0 :: int) \<le> j \<and> j < l \<longrightarrow> \<not>i = j \<longrightarrow> \<not>p ! nat i = p ! nat j)" for l p
definition permutation_pair :: "int \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> _"
  where "permutation_pair l p invp \<longleftrightarrow> permutation l p \<and> permutation l invp \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < l \<longrightarrow> p ! nat (invp ! nat i) = i) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < l \<longrightarrow> invp ! nat (p ! nat i) = i)" for l p invp
consts identity :: "int \<Rightarrow> int list"
axiomatization where identity'spec'1:   "int (length (identity l)) = l"
 if "(0 :: int) < l"
  for l :: "int"
axiomatization where identity'spec'0:   "identity l ! nat i = i"
 if "(0 :: int) < l"
 and "(0 :: int) \<le> i"
 and "i < l"
  for l :: "int"
  and i :: "int"
axiomatization where identity'spec:   "permutation_pair l (identity l) (identity l)"
 if "(0 :: int) < l"
  for l :: "int"
typedecl  elt
definition valid_chunk :: "elt list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "valid_chunk a ofs len \<longleftrightarrow> (0 :: int) \<le> ofs \<and> ofs \<le> ofs + len \<and> ofs + len \<le> int (length a)" for a ofs len
definition copy :: "elt list \<Rightarrow> elt list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "copy src dst ofs len \<longleftrightarrow> valid_chunk src ofs len \<and> length src = length dst \<and> (\<forall>(i :: int). ofs \<le> i \<and> i < ofs + len \<longrightarrow> dst ! nat i = src ! nat i)" for src dst ofs len
definition copy_to :: "elt list \<Rightarrow> elt list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "copy_to src dst ofss ofsd len \<longleftrightarrow> valid_chunk src ofss len \<and> valid_chunk dst ofsd len \<and> length src = length dst \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < len \<longrightarrow> dst ! nat (ofsd + i) = src ! nat (ofss + i)) \<and> (\<forall>(i :: int). ofsd \<le> i \<and> i < ofsd + len \<longrightarrow> dst ! nat i = src ! nat (i + (ofss - ofsd)))" for src dst ofss ofsd len
theorem smart_array_copy_0b'vc:
  fixes src :: "elt list"
  fixes dst :: "elt list"
  fixes k :: "int"
  fixes l :: "int"
  fixes q :: "int"
  fixes r :: "int"
  assumes fact0: "length src = length dst"
  assumes fact1: "(0 :: int) < int (length dst)"
  assumes fact2: "(0 :: int) < k"
  assumes fact3: "(0 :: int) < l"
  assumes fact4: "(0 :: int) \<le> q"
  assumes fact5: "(0 :: int) \<le> r"
  assumes fact6: "r < k * l"
  assumes fact7: "int (length dst) = q * k * l + r"
  shows "let m :: int = k * l; o1 :: int = q - (1 :: int) in ((0 :: int) \<le> o1 + (1 :: int) \<longrightarrow> copy src dst (0 :: int) ((0 :: int) * m) \<and> (\<forall>(dst1 :: elt list). length dst1 = length dst \<longrightarrow> (\<forall>(s :: int). ((0 :: int) \<le> s \<and> s \<le> o1) \<and> copy src dst1 (0 :: int) (s * m) \<longrightarrow> (let start :: int = s * m in (0 :: int) < l \<and> (\<forall>(sigma :: int list) (invsigma :: int list). (length sigma = length invsigma \<and> int (length invsigma) = l) \<and> permutation_pair l sigma invsigma \<longrightarrow> (let o2 :: int = l - (1 :: int) in ((0 :: int) \<le> o2 + (1 :: int) \<longrightarrow> (copy src dst1 (0 :: int) (s * m) \<and> (\<forall>(j' :: int). (0 :: int) \<le> j' \<and> j' < (0 :: int) \<longrightarrow> copy src dst1 (start + sigma ! nat j' * k) k)) \<and> (\<forall>(dst2 :: elt list). length dst2 = length dst1 \<longrightarrow> (\<forall>(j :: int). ((0 :: int) \<le> j \<and> j \<le> o2) \<and> copy src dst2 (0 :: int) (s * m) \<and> (\<forall>(j' :: int). (0 :: int) \<le> j' \<and> j' < j \<longrightarrow> copy src dst2 (start + sigma ! nat j' * k) k) \<longrightarrow> ((0 :: int) \<le> j \<and> j < int (length sigma)) \<and> (let startj :: int = start + sigma ! nat j * k in (length src = length dst2 \<and> valid_chunk src startj k \<and> valid_chunk dst2 startj k) \<and> (\<forall>(dst3 :: elt list). length dst3 = length dst2 \<longrightarrow> copy_to src dst3 startj startj k \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < startj \<longrightarrow> dst3 ! nat i = dst2 ! nat i) \<and> (\<forall>(i :: int). startj + k \<le> i \<and> i < int (length dst3) \<longrightarrow> dst3 ! nat i = dst2 ! nat i) \<longrightarrow> copy src dst3 (0 :: int) (s * m) \<and> (\<forall>(j' :: int). (0 :: int) \<le> j' \<and> j' < j + (1 :: int) \<longrightarrow> copy src dst3 (start + sigma ! nat j' * k) k)))) \<and> (copy src dst2 (0 :: int) (s * m) \<and> (\<forall>(j' :: int). (0 :: int) \<le> j' \<and> j' < o2 + (1 :: int) \<longrightarrow> copy src dst2 (start + sigma ! nat j' * k) k) \<longrightarrow> copy src dst2 (0 :: int) ((s + (1 :: int)) * m)))) \<and> (o2 + (1 :: int) < (0 :: int) \<longrightarrow> copy src dst1 (0 :: int) ((s + (1 :: int)) * m)))))) \<and> (copy src dst1 (0 :: int) ((o1 + (1 :: int)) * m) \<longrightarrow> (let last :: int = q * m in (length src = length dst1 \<and> valid_chunk src last r \<and> valid_chunk dst1 last r) \<and> (\<forall>(dst2 :: elt list). length dst2 = length dst1 \<longrightarrow> copy_to src dst2 last last r \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < last \<longrightarrow> dst2 ! nat i = dst1 ! nat i) \<and> (\<forall>(i :: int). last + r \<le> i \<and> i < int (length dst2) \<longrightarrow> dst2 ! nat i = dst1 ! nat i) \<longrightarrow> copy src dst2 (0 :: int) (int (length dst))))))) \<and> (o1 + (1 :: int) < (0 :: int) \<longrightarrow> (let last :: int = q * m in (length src = length dst \<and> valid_chunk src last r \<and> valid_chunk dst last r) \<and> (\<forall>(dst1 :: elt list). length dst1 = length dst \<longrightarrow> copy_to src dst1 last last r \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < last \<longrightarrow> dst1 ! nat i = dst ! nat i) \<and> (\<forall>(i :: int). last + r \<le> i \<and> i < int (length dst1) \<longrightarrow> dst1 ! nat i = dst ! nat i) \<longrightarrow> copy src dst1 (0 :: int) (int (length dst)))))"
  sorry
end
