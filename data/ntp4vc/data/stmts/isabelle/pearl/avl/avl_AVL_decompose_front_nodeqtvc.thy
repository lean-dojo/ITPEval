theory avl_AVL_decompose_front_nodeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  t
consts zero :: "t"
consts op :: "t \<Rightarrow> t \<Rightarrow> t"
axiomatization where assoc:   "op a (op b c) = op (op a b) c"
  for a :: "t"
  and b :: "t"
  and c :: "t"
axiomatization where neutral'0:   "op x zero = x"
  for x :: "t"
axiomatization where neutral'1:   "x = op zero x"
  for x :: "t"
consts agg :: "('a \<Rightarrow> t) \<Rightarrow> 'a list \<Rightarrow> t"
axiomatization where agg_empty:   "agg f ([] :: 'a list) = zero"
  for f :: "'a \<Rightarrow> t"
axiomatization where agg_sing:   "agg f s = f (s ! (0 :: nat))"
 if "int (length s) = (1 :: int)"
  for s :: "'a list"
  and f :: "'a \<Rightarrow> t"
axiomatization where agg_cat:   "agg f (s1 @ s2) = op (agg f s1) (agg f s2)"
  for f :: "'a \<Rightarrow> t"
  and s1 :: "'a list"
  and s2 :: "'a list"
typedecl 'a t1
consts measure :: "'a t1 \<Rightarrow> t"
consts balancing :: "nat"
axiomatization where balancing'def:   "(0 :: int) < int balancing"
datatype 'a tree = Empty | Node "'a tree" "'a t1" "'a tree" "nat" "t"
datatype 'a m = m'mk (seq: "'a t1 list") (hgt: "int")
definition node_model :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "node_model l d r = l @ Cons d r" for l d r
fun seq_model :: "'a tree \<Rightarrow> 'a t1 list"
  where "seq_model (Empty :: 'a tree) = ([] :: 'a t1 list)"
      | "seq_model (Node l d r x x0) = node_model (seq_model l) d (seq_model r)" for l d r x x0
fun real_height :: "'a tree \<Rightarrow> int"
  where "real_height (Empty :: 'a tree) = (0 :: int)"
      | "real_height (Node l x r x0 x1) = (let hl :: int = real_height l; hr :: int = real_height r in (1 :: int) + (if hl < hr then hr else hl))" for l x r x0 x1
consts measure_closure :: "'a t1 \<Rightarrow> t"
axiomatization where measure_closure_def:   "measure_closure y = measure y"
  for y :: "'a t1"
fun balanced :: "'a tree \<Rightarrow> _"
  where "balanced (Empty :: 'a tree) = True"
      | "balanced (Node l x r h m1) = (int h = real_height (Node l x r h m1) \<and> m1 = agg measure_closure (seq_model (Node l x r h m1)) \<and> (-int balancing \<le> real_height r - real_height l \<and> real_height r - real_height l \<le> int balancing) \<and> balanced l \<and> balanced r)" for l x r h m1
typedecl 'a t2
consts repr :: "'a t2 \<Rightarrow> 'a tree"
consts m1 :: "'a t2 \<Rightarrow> 'a m"
axiomatization where t'invariant'0:   "balanced (repr self)"
  for self :: "'a t2"
axiomatization where t'invariant'1:   "seq (m1 self) = seq_model (repr self)"
  for self :: "'a t2"
axiomatization where t'invariant'2:   "hgt (m1 self) = real_height (repr self)"
  for self :: "'a t2"
definition t'eq :: "'a t2 \<Rightarrow> 'a t2 \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> repr a = repr b \<and> m1 a = m1 b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "'a t2"
  and b :: "'a t2"
datatype 'a view = AEmpty | ANode "'a t2" "'a t1" "'a t2" "nat" "t"
theorem decompose_front_node'vc:
  fixes l :: "'a t2"
  fixes r :: "'a t2"
  fixes o1 :: "'a view"
  fixes d :: "'a t1"
  assumes fact0: "-int balancing \<le> hgt (m1 l) - hgt (m1 r)"
  assumes fact1: "hgt (m1 l) - hgt (m1 r) \<le> int balancing"
  assumes fact2: "case o1 of (AEmpty :: 'a view) \<Rightarrow> hgt (m1 l) = (0 :: int) \<and> seq (m1 l) = ([] :: 'a t1 list) | ANode l1 d r1 h s \<Rightarrow> seq (m1 l) = node_model (seq (m1 l1)) d (seq (m1 r1)) \<and> s = agg measure_closure (seq (m1 l)) \<and> (let hl :: int = hgt (m1 l1); hr :: int = hgt (m1 r1) in (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing) \<and> hgt (m1 l) = int h \<and> int h = (1 :: int) + (if hl < hr then hr else hl))"
  shows "case o1 of (AEmpty :: 'a view) \<Rightarrow> True | ANode l1 d2 r2 _ _ \<Rightarrow> (((0 :: int) \<le> hgt (m1 l) \<and> hgt (m1 l1) < hgt (m1 l)) \<and> -int balancing \<le> hgt (m1 l1) - hgt (m1 r2) \<and> hgt (m1 l1) - hgt (m1 r2) \<le> int balancing) \<and> (\<forall>(d3 :: 'a t1) (left1 :: 'a t2). node_model (seq (m1 l1)) d2 (seq (m1 r2)) = Cons d3 (seq (m1 left1)) \<and> (let hl :: int = hgt (m1 l1); hr :: int = hgt (m1 r2); he :: int = (1 :: int) + (if hl < hr then hr else hl) in (0 :: int) \<le> he - hgt (m1 left1) \<and> he - hgt (m1 left1) \<le> (1 :: int)) \<longrightarrow> -int balancing - (1 :: int) \<le> hgt (m1 left1) - hgt (m1 r) \<and> hgt (m1 left1) - hgt (m1 r) \<le> int balancing + (1 :: int))"
  and "\<forall>(d2 :: 'a t1) (res :: 'a t2). (case o1 of (AEmpty :: 'a view) \<Rightarrow> d2 = d \<and> res = r | ANode l1 d21 r2 _ _ \<Rightarrow> (\<exists>(res1 :: 'a t2). (node_model (seq (m1 l1)) d21 (seq (m1 r2)) = Cons d2 (seq (m1 res1)) \<and> (let hl :: int = hgt (m1 l1); hr :: int = hgt (m1 r2); he :: int = (1 :: int) + (if hl < hr then hr else hl) in (0 :: int) \<le> he - hgt (m1 res1) \<and> he - hgt (m1 res1) \<le> (1 :: int))) \<and> seq (m1 res) = node_model (seq (m1 res1)) d (seq (m1 r)) \<and> (let hl :: int = hgt (m1 res1); hr :: int = hgt (m1 r); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 res) in ((0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int)) \<and> (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing \<longrightarrow> he = hres)))) \<longrightarrow> node_model (seq (m1 l)) d (seq (m1 r)) = Cons d2 (seq (m1 res)) \<and> (let hl :: int = hgt (m1 l); hr :: int = hgt (m1 r); he :: int = (1 :: int) + (if hl < hr then hr else hl) in (0 :: int) \<le> he - hgt (m1 res) \<and> he - hgt (m1 res) \<le> (1 :: int))"
  sorry
end
