theory linear_probing_LinearProbing_removeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "Why3STD.map_Const"
begin
typedecl  key
typedecl  keym
consts keym1 :: "key \<Rightarrow> keym"
consts eq :: "key \<Rightarrow> key \<Rightarrow> bool"
axiomatization where eq'spec:   "eq x y \<longleftrightarrow> keym1 x = keym1 y"
  for x :: "key"
  and y :: "key"
definition neq :: "key \<Rightarrow> key \<Rightarrow> _"
  where "neq x y \<longleftrightarrow> \<not>eq x y" for x y
axiomatization where neq'spec:   "neq x y \<longleftrightarrow> \<not>keym1 x = keym1 y"
  for x :: "key"
  and y :: "key"
consts hash :: "key \<Rightarrow> int"
axiomatization where hash_nonneg:   "(0 :: int) \<le> hash k"
  for k :: "key"
axiomatization where hash_eq:   "hash x = hash y"
 if "eq x y"
  for x :: "key"
  and y :: "key"
consts dummy :: "key"
consts bucket :: "key \<Rightarrow> int \<Rightarrow> int"
axiomatization where bucket'def:   "bucket k n = hash k cmod n"
 if "(0 :: int) < n"
  for n :: "int"
  and k :: "key"
axiomatization where bucket'spec'0:   "(0 :: int) \<le> bucket k n"
 if "(0 :: int) < n"
  for n :: "int"
  and k :: "key"
axiomatization where bucket'spec'1:   "bucket k n < n"
 if "(0 :: int) < n"
  for n :: "int"
  and k :: "key"
definition between :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "between l j r \<longleftrightarrow> l \<le> j \<and> j < r \<or> r < l \<and> l \<le> j \<or> j < r \<and> r < l" for l j r
consts fc :: "key list \<Rightarrow> int \<Rightarrow> bool"
axiomatization where fc'def:   "fc a i = True \<longleftrightarrow> eq (a ! nat i) dummy"
  for a :: "key list"
  and i :: "int"
definition numof :: "key list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "numof a l u = int_NumOf.numof (fc a) l u" for a l u
definition valid :: "key list \<Rightarrow> (keym \<Rightarrow> bool) \<Rightarrow> (keym \<Rightarrow> int) \<Rightarrow> _"
  where "valid data view loc \<longleftrightarrow> \<not>view (keym1 dummy) = True \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length data) \<longrightarrow> (let x :: key = data ! nat i in neq x dummy \<longrightarrow> view (keym1 x) = True \<and> loc (keym1 x) = i)) \<and> (let n :: int = int (length data) in \<forall>(x :: key). view (keym1 x) = True \<longrightarrow> (let i :: int = loc (keym1 x) in ((0 :: int) \<le> i \<and> i < n) \<and> eq (data ! nat i) x \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < n \<longrightarrow> between (bucket x n) j i \<longrightarrow> neq (data ! nat j) x \<and> neq (data ! nat j) dummy)))" for data view loc
typedecl  t
consts size :: "t \<Rightarrow> int"
consts data :: "t \<Rightarrow> key list"
consts view :: "t \<Rightarrow> keym \<Rightarrow> bool"
consts loc :: "t \<Rightarrow> keym \<Rightarrow> int"
axiomatization where t'invariant'0:   "(0 :: int) \<le> size self"
  for self :: "t"
axiomatization where t'invariant'1:   "size self < int (length (data self))"
  for self :: "t"
axiomatization where t'invariant'2:   "size self + numof (data self) (0 :: int) (int (length (data self))) = int (length (data self))"
  for self :: "t"
axiomatization where t'invariant'3:   "valid (data self) (view self) (loc self)"
  for self :: "t"
definition t'eq :: "t \<Rightarrow> t \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> size a = size b \<and> data a = data b \<and> view a = view b \<and> loc a = loc b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "t"
  and b :: "t"
definition "next" :: "int \<Rightarrow> int \<Rightarrow> int"
  where "next n i = (let i1 :: int = i + (1 :: int) in if i1 = n then 0 :: int else i1)" for n i
theorem remove'vc:
  fixes x :: "key"
  fixes h :: "t"
  assumes fact0: "neq x dummy"
  shows "let o1 :: key list = data h in (neq x dummy \<and> (let n :: int = int (length o1) in (0 :: int) < n \<and> (0 :: int) < numof o1 (0 :: int) n)) \<and> (\<forall>(j :: int). ((0 :: int) \<le> j \<and> j < int (length o1)) \<and> (eq (o1 ! nat j) dummy \<or> eq (o1 ! nat j) x) \<and> (\<forall>(j1 :: int). (0 :: int) \<le> j1 \<and> j1 < int (length o1) \<longrightarrow> between (bucket x (int (length o1))) j1 j \<longrightarrow> neq (o1 ! nat j1) x \<and> neq (o1 ! nat j1) dummy) \<longrightarrow> (let o2 :: key = dummy; o3 :: key list = data h in ((0 :: int) \<le> j \<and> j < int (length o3)) \<and> (let o4 :: key = o3 ! nat j in (neq o4 o2 \<longleftrightarrow> \<not>keym1 o4 = keym1 o2) \<longrightarrow> (if neq o4 o2 then let o5 :: key = dummy; o6 :: key list = data h in ((0 :: int) \<le> j \<and> j < int (length o6)) \<and> (length (o6[nat j := o5]) = length o6 \<longrightarrow> length (o6[nat j := o5]) = length (data h) \<longrightarrow> nth (o6[nat j := o5]) o nat = (nth o6 o nat)(j := o5) \<longrightarrow> (let o7 :: int = next (int (length (data h))) j in (((0 :: int) \<le> j \<and> j < int (length (o6[nat j := o5]))) \<and> ((0 :: int) \<le> o7 \<and> o7 < int (length (o6[nat j := o5]))) \<and> \<not>o7 = j \<and> (if j \<le> o7 then (1 :: int) \<le> numof (o6[nat j := o5]) o7 (int (length (o6[nat j := o5]))) + numof (o6[nat j := o5]) (0 :: int) j else (1 :: int) \<le> numof (o6[nat j := o5]) o7 j) \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length (o6[nat j := o5])) \<longrightarrow> between j k o7 \<longrightarrow> \<not>k = j \<longrightarrow> neq (o6[nat j := o5] ! nat k) dummy)) \<and> (\<forall>(f0 :: int). ((0 :: int) \<le> f0 \<and> f0 < int (length (o6[nat j := o5]))) \<and> \<not>f0 = j \<and> eq (o6[nat j := o5] ! nat f0) dummy \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length (o6[nat j := o5])) \<longrightarrow> between j k f0 \<longrightarrow> \<not>k = j \<longrightarrow> neq (o6[nat j := o5] ! nat k) dummy) \<longrightarrow> (((0 :: int) \<le> f0 \<and> f0 < int (length (o6[nat j := o5]))) \<and> ((0 :: int) \<le> j \<and> j < int (length (o6[nat j := o5]))) \<and> ((0 :: int) \<le> j \<and> j < int (length (o6[nat j := o5]))) \<and> \<not>j = f0 \<and> eq (o6[nat j := o5] ! nat j) dummy \<and> eq (o6[nat j := o5] ! nat f0) dummy \<and> between j j f0 \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length (o6[nat j := o5])) \<longrightarrow> between j k f0 \<longrightarrow> \<not>k = j \<longrightarrow> neq (o6[nat j := o5] ! nat k) dummy) \<and> \<not>((view h)(keym1 x := False)) (keym1 dummy) = True \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < int (length (o6[nat j := o5])) \<longrightarrow> (let x1 :: key = o6[nat j := o5] ! nat k in neq x1 dummy \<longrightarrow> ((view h)(keym1 x := False)) (keym1 x1) = True \<and> loc h (keym1 x1) = k)) \<and> (let n :: int = int (length (o6[nat j := o5])) in \<forall>(x1 :: key). ((view h)(keym1 x := False)) (keym1 x1) = True \<longrightarrow> (let k :: int = loc h (keym1 x1) in ((0 :: int) \<le> k \<and> k < n) \<and> eq (o6[nat j := o5] ! nat k) x1 \<and> (\<forall>(l :: int). (0 :: int) \<le> l \<and> l < n \<longrightarrow> between (bucket x1 n) l k \<longrightarrow> neq (o6[nat j := o5] ! nat l) x1 \<and> (neq (o6[nat j := o5] ! nat l) dummy \<or> l = j \<and> between j j k))))) \<and> (\<forall>(l :: keym \<Rightarrow> int) (h_data :: key list). length h_data = length (o6[nat j := o5]) \<longrightarrow> length h_data = length (o6[nat j := o5]) \<longrightarrow> numof h_data (0 :: int) (int (length h_data)) = numof (o6[nat j := o5]) (0 :: int) (int (length h_data)) \<and> valid h_data ((view h)(keym1 x := False)) l \<longrightarrow> (\<forall>(h1 :: t). (((0 :: int) \<le> size h - (1 :: int) \<and> size h - (1 :: int) < int (length h_data)) \<and> (let n :: int = int (length h_data) in size h - (1 :: int) + numof h_data (0 :: int) n = n) \<and> valid h_data ((view h)(keym1 x := False)) l) \<and> (l = loc h1 \<and> (view h)(keym1 x := False) = view h1 \<and> h_data = data h1 \<and> size h - (1 :: int) = size h1 \<longrightarrow> view h1 = (view h)(keym1 x := False))))))) else view h = (view h)(keym1 x := False)))))"
  sorry
end
