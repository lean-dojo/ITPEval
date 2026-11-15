theory linear_probing_LinearProbing_resizeqtvc
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
theorem resize'vc:
  fixes h :: "t"
  shows "let n :: int = int (length (data h)); n2 :: int = (2 :: int) * n in (0 :: int) \<le> n2 \<and> (\<forall>(a :: key list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n2 \<longrightarrow> a ! nat i = dummy) \<and> int (length a) = n2 \<longrightarrow> (let o1 :: keym \<Rightarrow> int = (const :: int \<Rightarrow> keym \<Rightarrow> int) (0 :: int); o2 :: int = n - (1 :: int) in ((0 :: int) \<le> o2 + (1 :: int) \<longrightarrow> (numof a (0 :: int) n2 = numof (data h) (0 :: int) (0 :: int) + n2 - (0 :: int) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < n2 \<longrightarrow> neq (a ! nat j) dummy \<longrightarrow> view h (keym1 (a ! nat j)) = True \<and> o1 (keym1 (a ! nat j)) = j) \<and> (\<forall>(x :: key). view h (keym1 x) = True \<longrightarrow> (if loc h (keym1 x) < (0 :: int) then let j2 :: int = o1 (keym1 x) in ((0 :: int) \<le> j2 \<and> j2 < n2) \<and> eq (a ! nat j2) x \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < n2 \<longrightarrow> between (bucket x n2) k j2 \<longrightarrow> neq (a ! nat k) x \<and> neq (a ! nat k) dummy) else \<forall>(j2 :: int). (0 :: int) \<le> j2 \<and> j2 < n2 \<longrightarrow> neq (a ! nat j2) x))) \<and> (\<forall>(l :: keym \<Rightarrow> int) (a1 :: key list). length a1 = length a \<longrightarrow> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i \<le> o2) \<and> numof a1 (0 :: int) n2 = numof (data h) (0 :: int) i + n2 - i \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < n2 \<longrightarrow> neq (a1 ! nat j) dummy \<longrightarrow> view h (keym1 (a1 ! nat j)) = True \<and> l (keym1 (a1 ! nat j)) = j) \<and> (\<forall>(x :: key). view h (keym1 x) = True \<longrightarrow> (if loc h (keym1 x) < i then let j2 :: int = l (keym1 x) in ((0 :: int) \<le> j2 \<and> j2 < n2) \<and> eq (a1 ! nat j2) x \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < n2 \<longrightarrow> between (bucket x n2) k j2 \<longrightarrow> neq (a1 ! nat k) x \<and> neq (a1 ! nat k) dummy) else \<forall>(j2 :: int). (0 :: int) \<le> j2 \<and> j2 < n2 \<longrightarrow> neq (a1 ! nat j2) x)) \<longrightarrow> (let o3 :: key list = data h in ((0 :: int) \<le> i \<and> i < int (length o3)) \<and> (let x :: key = o3 ! nat i; o4 :: key = dummy in (neq x o4 \<longleftrightarrow> \<not>keym1 x = keym1 o4) \<longrightarrow> (if neq x o4 then (neq x dummy \<and> (let n1 :: int = int (length a1) in (0 :: int) < n1 \<and> (0 :: int) < numof a1 (0 :: int) n1)) \<and> (\<forall>(j :: int). ((0 :: int) \<le> j \<and> j < int (length a1)) \<and> (eq (a1 ! nat j) dummy \<or> eq (a1 ! nat j) x) \<and> (\<forall>(j1 :: int). (0 :: int) \<le> j1 \<and> j1 < int (length a1) \<longrightarrow> between (bucket x (int (length a1))) j1 j \<longrightarrow> neq (a1 ! nat j1) x \<and> neq (a1 ! nat j1) dummy) \<longrightarrow> ((0 :: int) \<le> j \<and> j < int (length a1)) \<and> (length (a1[nat j := x]) = length a1 \<longrightarrow> nth (a1[nat j := x]) o nat = (nth a1 o nat)(j := x) \<longrightarrow> numof (a1[nat j := x]) (0 :: int) n2 = numof (data h) (0 :: int) (i + (1 :: int)) + n2 - (i + (1 :: int)) \<and> (\<forall>(j1 :: int). (0 :: int) \<le> j1 \<and> j1 < n2 \<longrightarrow> neq (a1[nat j := x] ! nat j1) dummy \<longrightarrow> view h (keym1 (a1[nat j := x] ! nat j1)) = True \<and> (l(keym1 x := j)) (keym1 (a1[nat j := x] ! nat j1)) = j1) \<and> (\<forall>(x1 :: key). view h (keym1 x1) = True \<longrightarrow> (if loc h (keym1 x1) < i + (1 :: int) then let j2 :: int = (l(keym1 x := j)) (keym1 x1) in ((0 :: int) \<le> j2 \<and> j2 < n2) \<and> eq (a1[nat j := x] ! nat j2) x1 \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < n2 \<longrightarrow> between (bucket x1 n2) k j2 \<longrightarrow> neq (a1[nat j := x] ! nat k) x1 \<and> neq (a1[nat j := x] ! nat k) dummy) else \<forall>(j2 :: int). (0 :: int) \<le> j2 \<and> j2 < n2 \<longrightarrow> neq (a1[nat j := x] ! nat j2) x1)))) else numof a1 (0 :: int) n2 = numof (data h) (0 :: int) (i + (1 :: int)) + n2 - (i + (1 :: int)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < n2 \<longrightarrow> neq (a1 ! nat j) dummy \<longrightarrow> view h (keym1 (a1 ! nat j)) = True \<and> l (keym1 (a1 ! nat j)) = j) \<and> (\<forall>(x1 :: key). view h (keym1 x1) = True \<longrightarrow> (if loc h (keym1 x1) < i + (1 :: int) then let j2 :: int = l (keym1 x1) in ((0 :: int) \<le> j2 \<and> j2 < n2) \<and> eq (a1 ! nat j2) x1 \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < n2 \<longrightarrow> between (bucket x1 n2) k j2 \<longrightarrow> neq (a1 ! nat k) x1 \<and> neq (a1 ! nat k) dummy) else \<forall>(j2 :: int). (0 :: int) \<le> j2 \<and> j2 < n2 \<longrightarrow> neq (a1 ! nat j2) x1)))))) \<and> (numof a1 (0 :: int) n2 = numof (data h) (0 :: int) (o2 + (1 :: int)) + n2 - (o2 + (1 :: int)) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < n2 \<longrightarrow> neq (a1 ! nat j) dummy \<longrightarrow> view h (keym1 (a1 ! nat j)) = True \<and> l (keym1 (a1 ! nat j)) = j) \<and> (\<forall>(x :: key). view h (keym1 x) = True \<longrightarrow> (if loc h (keym1 x) < o2 + (1 :: int) then let j2 :: int = l (keym1 x) in ((0 :: int) \<le> j2 \<and> j2 < n2) \<and> eq (a1 ! nat j2) x \<and> (\<forall>(k :: int). (0 :: int) \<le> k \<and> k < n2 \<longrightarrow> between (bucket x n2) k j2 \<longrightarrow> neq (a1 ! nat k) x \<and> neq (a1 ! nat k) dummy) else \<forall>(j2 :: int). (0 :: int) \<le> j2 \<and> j2 < n2 \<longrightarrow> neq (a1 ! nat j2) x)) \<longrightarrow> (\<forall>(h1 :: t). (((0 :: int) \<le> size h \<and> size h < int (length a1)) \<and> (let n3 :: int = int (length a1) in size h + numof a1 (0 :: int) n3 = n3) \<and> valid a1 (view h) l) \<and> (l = loc h1 \<and> view h = view h1 \<and> a1 = data h1 \<and> size h = size h1 \<longrightarrow> int (length (data h1)) = (2 :: int) * int (length (data h))))))) \<and> (o2 + (1 :: int) < (0 :: int) \<longrightarrow> (\<forall>(h1 :: t). (((0 :: int) \<le> size h \<and> size h < int (length a)) \<and> (let n3 :: int = int (length a) in size h + numof a (0 :: int) n3 = n3) \<and> valid a (view h) o1) \<and> (o1 = loc h1 \<and> view h = view h1 \<and> a = data h1 \<and> size h = size h1 \<longrightarrow> int (length (data h1)) = (2 :: int) * int (length (data h)))))))"
  sorry
end
