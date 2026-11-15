theory tables_MapBase_joinqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "../../lib/isabelle/avl_SelectionTypes"
begin
consts balancing :: "nat"
axiomatization where balancing'def:   "(0 :: int) < int balancing"
typedecl 'a t
typedecl  t1
consts key :: "'a t \<Rightarrow> t1"
consts le :: "t1 \<Rightarrow> t1 \<Rightarrow> bool"
axiomatization where Refl:   "le x x"
  for x :: "t1"
axiomatization where Trans:   "le x z"
 if "le x y"
 and "le y z"
  for x :: "t1"
  and y :: "t1"
  and z :: "t1"
consts eq :: "t1 \<Rightarrow> t1 \<Rightarrow> bool"
axiomatization where eq_def:   "eq x y \<longleftrightarrow> le x y \<and> le y x"
  for x :: "t1"
  and y :: "t1"
consts lt :: "t1 \<Rightarrow> t1 \<Rightarrow> bool"
axiomatization where lt_def:   "lt x y \<longleftrightarrow> le x y \<and> \<not>le y x"
  for x :: "t1"
  and y :: "t1"
axiomatization where Total:   "le x y \<or> le y x"
  for x :: "t1"
  and y :: "t1"
typedecl  t2
axiomatization where assoc:   "True"
axiomatization where neutral'0:   "() = x"
  for x :: "unit"
axiomatization where neutral'1:   "x = ()"
  for x :: "unit"
typedecl  selector
definition selection_possible :: "'b \<Rightarrow> 'a t list \<Rightarrow> _"
  where "selection_possible x s \<longleftrightarrow> (\<forall>(i :: int) (j :: int). (0 :: int) \<le> i \<and> i < j \<and> j < int (length s) \<longrightarrow> lt (key (s ! nat i)) (key (s ! nat j)))" for x s
definition upper_bound_s :: "t1 \<Rightarrow> 'a t list \<Rightarrow> _"
  where "upper_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt (key (s ! nat i)) k)" for k s
definition lower_bound_s :: "t1 \<Rightarrow> 'a t list \<Rightarrow> _"
  where "lower_bound_s k s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt k (key (s ! nat i)))" for k s
definition selected :: "t1 \<Rightarrow> 'a t split \<Rightarrow> _"
  where "selected k e \<longleftrightarrow> upper_bound_s k (left1 e) \<and> lower_bound_s k (right1 e) \<and> (case middle e of (None :: 'a t option) \<Rightarrow> True | Some d \<Rightarrow> eq k (key d))" for k e
datatype 'a tree = Empty | Node "'a tree" "'a t" "'a tree" "nat" "unit"
datatype 'a m = m'mk (seq: "'a t list") (hgt: "int")
definition node_model :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "node_model l d r = l @ Cons d r" for l d r
fun seq_model :: "'a tree \<Rightarrow> 'a t list"
  where "seq_model (Empty :: 'a tree) = ([] :: 'a t list)"
      | "seq_model (Node l d r x x0) = node_model (seq_model l) d (seq_model r)" for l d r x x0
fun real_height :: "'a tree \<Rightarrow> int"
  where "real_height (Empty :: 'a tree) = (0 :: int)"
      | "real_height (Node l x r x0 x1) = (let hl :: int = real_height l; hr :: int = real_height r in (1 :: int) + (if hl < hr then hr else hl))" for l x r x0 x1
fun balanced :: "'a tree \<Rightarrow> _"
  where "balanced (Empty :: 'a tree) = True"
      | "balanced (Node l x r h m1) = (int h = real_height (Node l x r h m1) \<and> m1 = () \<and> (-int balancing \<le> real_height r - real_height l \<and> real_height r - real_height l \<le> int balancing) \<and> balanced l \<and> balanced r)" for l x r h m1
typedecl 'a t3
consts repr :: "'a t3 \<Rightarrow> 'a tree"
consts m1 :: "'a t3 \<Rightarrow> 'a m"
axiomatization where t'invariant'0:   "balanced (repr self)"
  for self :: "'a t3"
axiomatization where t'invariant'1:   "seq (m1 self) = seq_model (repr self)"
  for self :: "'a t3"
axiomatization where t'invariant'2:   "hgt (m1 self) = real_height (repr self)"
  for self :: "'a t3"
definition t'eq :: "'a t3 \<Rightarrow> 'a t3 \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> repr a = repr b \<and> m1 a = m1 b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "'a t3"
  and b :: "'a t3"
datatype 'a view = AEmpty | ANode "'a t3" "'a t" "'a t3" "nat" "unit"
typedecl  part
typedecl 'a t4
consts field :: "'a t4 \<Rightarrow> 'a t3"
axiomatization where t'invariant1:   "selection_possible () (seq (m1 (field self)))"
  for self :: "'a t4"
definition t'eq1 :: "'a t4 \<Rightarrow> 'a t4 \<Rightarrow> _"
  where "t'eq1 a b \<longleftrightarrow> field a = field b" for a b
axiomatization where t'inj1:   "a = b"
 if "t'eq1 a b"
  for a :: "'a t4"
  and b :: "'a t4"
datatype 'a m2 = m'mk1 (domn: "t1 \<Rightarrow> bool") (func: "t1 \<Rightarrow> 'a t") (card: "int")
definition domain :: "'a t list \<Rightarrow> t1 \<Rightarrow> _"
  where "domain s k \<longleftrightarrow> (\<exists>(i :: int). ((0 :: int) \<le> i \<and> i < int (length s)) \<and> eq (key (s ! nat i)) k)" for s k
consts make_func :: "'a t list \<Rightarrow> t1 \<Rightarrow> 'a t"
axiomatization where make_func'spec:   "make_func s k = s ! nat i"
 if "selection_possible () s"
 and "domain s k"
 and "(0 :: int) \<le> i"
 and "i < int (length s)"
 and "eq (key (s ! nat i)) k"
  for s :: "'a t list"
  and k :: "t1"
  and i :: "int"
consts domain_closure :: "'a t list \<Rightarrow> t1 \<Rightarrow> bool"
consts make_func_closure :: "'a t list \<Rightarrow> t1 \<Rightarrow> 'a t"
axiomatization where domain_closure_def:   "domain_closure y y1 = True \<longleftrightarrow> domain y y1"
  for y :: "'a t list"
  and y1 :: "t1"
axiomatization where make_func_closure_def:   "make_func_closure y y1 = make_func y y1"
  for y :: "'a t list"
  and y1 :: "t1"
definition m3 :: "'a t4 \<Rightarrow> 'a m2"
  where "m3 t5 = (m'mk1 :: (t1 \<Rightarrow> bool) \<Rightarrow> (t1 \<Rightarrow> 'a t) \<Rightarrow> int \<Rightarrow> 'a m2) (domain_closure (seq (m1 (field t5)))) (make_func_closure (seq (m1 (field t5)))) (int (length (seq (m1 (field t5)))))" for t5
datatype 'a view1 = AEmpty1 | ANode1 "'a t4" "'a t" "'a t4" "nat"
theorem join'vc:
  fixes l :: "'a t4"
  fixes d :: "'a t"
  fixes r :: "'a t4"
  assumes fact0: "\<forall>(k :: t1). domn (m3 l) k = True \<longrightarrow> lt k (key d)"
  assumes fact1: "\<forall>(k :: t1). domn (m3 r) k = True \<longrightarrow> lt (key d) k"
  shows "let o1 :: 'a t3 = field r; o2 :: 'a t3 = field l in \<forall>(o3 :: 'a t3). seq (m1 o3) = node_model (seq (m1 o2)) d (seq (m1 o1)) \<and> (let hl :: int = hgt (m1 o2); hr :: int = hgt (m1 o1); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 o3) in (0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int)) \<longrightarrow> selection_possible () (seq (m1 o3)) \<and> (\<forall>(result :: 'a t4). field result = o3 \<longrightarrow> (\<forall>(k :: t1). lt k (key d) \<longrightarrow> domn (m3 result) k = True \<longleftrightarrow> domn (m3 l) k = True) \<and> (\<forall>(k :: t1). lt k (key d) \<and> domn (m3 result) k = True \<longrightarrow> func (m3 result) k = func (m3 l) k) \<and> (\<forall>(k :: t1). lt (key d) k \<longrightarrow> domn (m3 result) k = True \<longleftrightarrow> domn (m3 r) k = True) \<and> (\<forall>(k :: t1). lt (key d) k \<and> domn (m3 result) k = True \<longrightarrow> func (m3 result) k = func (m3 r) k) \<and> (\<forall>(k :: t1). eq k (key d) \<longrightarrow> domn (m3 result) k = True \<and> func (m3 result) k = d) \<and> card (m3 result) = (1 :: int) + card (m3 l) + card (m3 r))"
  sorry
end
