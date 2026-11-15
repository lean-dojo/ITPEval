theory avl_AVL_joinqtvc
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
theorem join'vc:
  fixes o1 :: "'a view"
  fixes l :: "'a t2"
  fixes r :: "'a t2"
  fixes d :: "'a t1"
  assumes fact0: "case o1 of (AEmpty :: 'a view) \<Rightarrow> hgt (m1 l) = (0 :: int) \<and> seq (m1 l) = ([] :: 'a t1 list) | ANode l1 d r h s \<Rightarrow> seq (m1 l) = node_model (seq (m1 l1)) d (seq (m1 r)) \<and> s = agg measure_closure (seq (m1 l)) \<and> (let hl :: int = hgt (m1 l1); hr :: int = hgt (m1 r) in (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing) \<and> hgt (m1 l) = int h \<and> int h = (1 :: int) + (if hl < hr then hr else hl))"
  shows "case o1 of (AEmpty :: 'a view) \<Rightarrow> True | ANode ll ld lr lh _ \<Rightarrow> (\<forall>(o2 :: 'a view). (case o2 of (AEmpty :: 'a view) \<Rightarrow> hgt (m1 r) = (0 :: int) \<and> seq (m1 r) = ([] :: 'a t1 list) | ANode l1 d r1 h s \<Rightarrow> seq (m1 r) = node_model (seq (m1 l1)) d (seq (m1 r1)) \<and> s = agg measure_closure (seq (m1 r)) \<and> (let hl :: int = hgt (m1 l1); hr :: int = hgt (m1 r1) in (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing) \<and> hgt (m1 r) = int h \<and> int h = (1 :: int) + (if hl < hr then hr else hl))) \<longrightarrow> (case o2 of (AEmpty :: 'a view) \<Rightarrow> True | ANode rl rd rr rh _ \<Rightarrow> (\<forall>(o3 :: nat). int o3 = -int rh \<longrightarrow> (int o3 \<le> int lh - int rh \<and> int lh - int rh \<le> int lh) \<and> (\<forall>(df :: nat). int df = int lh - int rh \<longrightarrow> (if balancing < df then ((0 :: int) \<le> (if hgt (m1 r) < hgt (m1 l) then hgt (m1 l) - hgt (m1 r) else hgt (m1 r) - hgt (m1 l)) \<and> (if hgt (m1 r) < hgt (m1 lr) then hgt (m1 lr) - hgt (m1 r) else hgt (m1 r) - hgt (m1 lr)) < (if hgt (m1 r) < hgt (m1 l) then hgt (m1 l) - hgt (m1 r) else hgt (m1 r) - hgt (m1 l))) \<and> (\<forall>(o4 :: 'a t2). seq (m1 o4) = node_model (seq (m1 lr)) d (seq (m1 r)) \<and> (let hl :: int = hgt (m1 lr); hr :: int = hgt (m1 r); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 o4) in (0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int)) \<longrightarrow> -int balancing - (1 :: int) \<le> hgt (m1 ll) - hgt (m1 o4) \<and> hgt (m1 ll) - hgt (m1 o4) \<le> int balancing + (1 :: int)) else \<forall>(o4 :: nat). int o4 = -int balancing \<longrightarrow> (if df < o4 then ((0 :: int) \<le> (if hgt (m1 r) < hgt (m1 l) then hgt (m1 l) - hgt (m1 r) else hgt (m1 r) - hgt (m1 l)) \<and> (if hgt (m1 rl) < hgt (m1 l) then hgt (m1 l) - hgt (m1 rl) else hgt (m1 rl) - hgt (m1 l)) < (if hgt (m1 r) < hgt (m1 l) then hgt (m1 l) - hgt (m1 r) else hgt (m1 r) - hgt (m1 l))) \<and> (\<forall>(o5 :: 'a t2). seq (m1 o5) = node_model (seq (m1 l)) d (seq (m1 rl)) \<and> (let hl :: int = hgt (m1 l); hr :: int = hgt (m1 rl); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 o5) in (0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int)) \<longrightarrow> -int balancing - (1 :: int) \<le> hgt (m1 o5) - hgt (m1 rr) \<and> hgt (m1 o5) - hgt (m1 rr) \<le> int balancing + (1 :: int)) else -int balancing \<le> hgt (m1 l) - hgt (m1 r) \<and> hgt (m1 l) - hgt (m1 r) \<le> int balancing))))))"
  and "\<forall>(result :: 'a t2). (case o1 of (AEmpty :: 'a view) \<Rightarrow> seq (m1 result) = Cons d (seq (m1 r)) \<and> hgt (m1 result) - hgt (m1 r) \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 result) - hgt (m1 r) | ANode ll ld lr lh _ \<Rightarrow> (\<exists>(o2 :: 'a view). (case o2 of (AEmpty :: 'a view) \<Rightarrow> hgt (m1 r) = (0 :: int) \<and> seq (m1 r) = ([] :: 'a t1 list) | ANode l1 d1 r1 h s \<Rightarrow> seq (m1 r) = node_model (seq (m1 l1)) d1 (seq (m1 r1)) \<and> s = agg measure_closure (seq (m1 r)) \<and> (let hl :: int = hgt (m1 l1); hr :: int = hgt (m1 r1) in (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing) \<and> hgt (m1 r) = int h \<and> int h = (1 :: int) + (if hl < hr then hr else hl))) \<and> (case o2 of (AEmpty :: 'a view) \<Rightarrow> seq (m1 result) = seq (m1 l) @ [d] \<and> hgt (m1 result) - hgt (m1 l) \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 result) - hgt (m1 l) | ANode rl rd rr rh _ \<Rightarrow> (\<exists>(o3 :: nat). int o3 = -int rh \<and> (\<exists>(df :: nat). int df = int lh - int rh \<and> (if balancing < df then \<exists>(o4 :: 'a t2). (seq (m1 o4) = node_model (seq (m1 lr)) d (seq (m1 r)) \<and> (let hl :: int = hgt (m1 lr); hr :: int = hgt (m1 r); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 o4) in (0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int))) \<and> seq (m1 result) = node_model (seq (m1 ll)) ld (seq (m1 o4)) \<and> (let hl :: int = hgt (m1 ll); hr :: int = hgt (m1 o4); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 result) in ((0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int)) \<and> (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing \<longrightarrow> he = hres)) else \<exists>(o4 :: nat). int o4 = -int balancing \<and> (if df < o4 then \<exists>(o5 :: 'a t2). (seq (m1 o5) = node_model (seq (m1 l)) d (seq (m1 rl)) \<and> (let hl :: int = hgt (m1 l); hr :: int = hgt (m1 rl); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 o5) in (0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int))) \<and> seq (m1 result) = node_model (seq (m1 o5)) rd (seq (m1 rr)) \<and> (let hl :: int = hgt (m1 o5); hr :: int = hgt (m1 rr); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 result) in ((0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int)) \<and> (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing \<longrightarrow> he = hres)) else seq (m1 result) = node_model (seq (m1 l)) d (seq (m1 r)) \<and> hgt (m1 result) = (1 :: int) + (if hgt (m1 l) < hgt (m1 r) then hgt (m1 r) else hgt (m1 l))))))))) \<longrightarrow> seq (m1 result) = node_model (seq (m1 l)) d (seq (m1 r)) \<and> (let hl :: int = hgt (m1 l); hr :: int = hgt (m1 r); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 result) in (0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int))"
  sorry
end
