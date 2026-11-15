theory avl_AVL_insertqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "../../lib/isabelle/avl_SelectionTypes"
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
typedecl  selector
consts selected :: "selector \<Rightarrow> 'a t1 split \<Rightarrow> bool"
consts selection_possible :: "selector \<Rightarrow> 'a t1 list \<Rightarrow> bool"
axiomatization where selection_empty:   "selection_possible s ([] :: 'a t1 list) \<longrightarrow> selected s (split'mk ([] :: 'a t1 list) (None :: 'a t1 option) ([] :: 'a t1 list))"
  for s :: "selector"
typedecl  part
theorem insert'vc:
  fixes s :: "selector"
  fixes t3 :: "'a t2"
  fixes o1 :: "'a view"
  fixes d :: "'a t1"
  assumes fact0: "selection_possible s (seq (m1 t3))"
  assumes fact1: "case o1 of (AEmpty :: 'a view) \<Rightarrow> hgt (m1 t3) = (0 :: int) \<and> seq (m1 t3) = ([] :: 'a t1 list) | ANode l d r h s1 \<Rightarrow> seq (m1 t3) = node_model (seq (m1 l)) d (seq (m1 r)) \<and> s1 = agg measure_closure (seq (m1 t3)) \<and> (let hl :: int = hgt (m1 l); hr :: int = hgt (m1 r) in (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing) \<and> hgt (m1 t3) = int h \<and> int h = (1 :: int) + (if hl < hr then hr else hl))"
  shows "case o1 of (AEmpty :: 'a view) \<Rightarrow> (\<forall>(result :: 'a t2). seq (m1 result) = [d] \<and> hgt (m1 result) = (1 :: int) \<longrightarrow> seq (m1 result) = node_model (left1 (split'mk ([] :: 'a t1 list) (None :: 'a t1 option) ([] :: 'a t1 list))) d (right1 (split'mk ([] :: 'a t1 list) (None :: 'a t1 option) ([] :: 'a t1 list))) \<and> (selected s (split'mk ([] :: 'a t1 list) (None :: 'a t1 option) ([] :: 'a t1 list)) \<and> rebuild (split'mk ([] :: 'a t1 list) (None :: 'a t1 option) ([] :: 'a t1 list)) = seq (m1 t3)) \<and> hgt (m1 result) - hgt (m1 t3) \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 result) - hgt (m1 t3)) | ANode tl' td tr _ _ \<Rightarrow> (let o2 :: 'a t1 list = seq (m1 tr); o3 :: 'a t1 list = seq (m1 tl') in (selection_possible s (node_model o3 td o2) \<and> agg measure_closure (seq (m1 tl')) = agg measure_closure o3 \<and> agg measure_closure (seq (m1 tr)) = agg measure_closure o2) \<and> (\<forall>(o4 :: selector part_base). (case o4 of Here \<Rightarrow> selected s (split'mk o3 (Some td) o2) | Left sl \<Rightarrow> selection_possible sl o3 \<and> (\<forall>(e :: 'a t1 split). selected sl e \<and> rebuild e = o3 \<longrightarrow> selected s (right_extend e td o2)) | Right sr \<Rightarrow> selection_possible sr o2 \<and> (\<forall>(e :: 'a t1 split). selected sr e \<and> rebuild e = o2 \<longrightarrow> selected s (left_extend o3 td e))) \<longrightarrow> (case o4 of Left sl \<Rightarrow> (((0 :: int) \<le> hgt (m1 t3) \<and> hgt (m1 tl') < hgt (m1 t3)) \<and> selection_possible sl (seq (m1 tl'))) \<and> (\<forall>(r :: 'a t1 split) (nl :: 'a t2). seq (m1 nl) = node_model (left1 r) d (right1 r) \<and> (selected sl r \<and> rebuild r = seq (m1 tl')) \<and> hgt (m1 nl) - hgt (m1 tl') \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 nl) - hgt (m1 tl') \<longrightarrow> (-int balancing - (1 :: int) \<le> hgt (m1 nl) - hgt (m1 tr) \<and> hgt (m1 nl) - hgt (m1 tr) \<le> int balancing + (1 :: int)) \<and> (\<forall>(result :: 'a t2). seq (m1 result) = node_model (seq (m1 nl)) td (seq (m1 tr)) \<and> (let hl :: int = hgt (m1 nl); hr :: int = hgt (m1 tr); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 result) in ((0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int)) \<and> (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing \<longrightarrow> he = hres)) \<longrightarrow> seq (m1 result) = node_model (left1 (right_extend r td (seq (m1 tr)))) d (right1 (right_extend r td (seq (m1 tr)))) \<and> (selected s (right_extend r td (seq (m1 tr))) \<and> rebuild (right_extend r td (seq (m1 tr))) = seq (m1 t3)) \<and> hgt (m1 result) - hgt (m1 t3) \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 result) - hgt (m1 t3))) | Right sr \<Rightarrow> (((0 :: int) \<le> hgt (m1 t3) \<and> hgt (m1 tr) < hgt (m1 t3)) \<and> selection_possible sr (seq (m1 tr))) \<and> (\<forall>(r :: 'a t1 split) (nr :: 'a t2). seq (m1 nr) = node_model (left1 r) d (right1 r) \<and> (selected sr r \<and> rebuild r = seq (m1 tr)) \<and> hgt (m1 nr) - hgt (m1 tr) \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 nr) - hgt (m1 tr) \<longrightarrow> (-int balancing - (1 :: int) \<le> hgt (m1 tl') - hgt (m1 nr) \<and> hgt (m1 tl') - hgt (m1 nr) \<le> int balancing + (1 :: int)) \<and> (\<forall>(result :: 'a t2). seq (m1 result) = node_model (seq (m1 tl')) td (seq (m1 nr)) \<and> (let hl :: int = hgt (m1 tl'); hr :: int = hgt (m1 nr); he :: int = (1 :: int) + (if hl < hr then hr else hl); hres :: int = hgt (m1 result) in ((0 :: int) \<le> he - hres \<and> he - hres \<le> (1 :: int)) \<and> (-int balancing \<le> hl - hr \<and> hl - hr \<le> int balancing \<longrightarrow> he = hres)) \<longrightarrow> seq (m1 result) = node_model (left1 (left_extend (seq (m1 tl')) td r)) d (right1 (left_extend (seq (m1 tl')) td r)) \<and> (selected s (left_extend (seq (m1 tl')) td r) \<and> rebuild (left_extend (seq (m1 tl')) td r) = seq (m1 t3)) \<and> hgt (m1 result) - hgt (m1 t3) \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 result) - hgt (m1 t3))) | Here \<Rightarrow> (-int balancing \<le> hgt (m1 tl') - hgt (m1 tr) \<and> hgt (m1 tl') - hgt (m1 tr) \<le> int balancing) \<and> (\<forall>(result :: 'a t2). seq (m1 result) = node_model (seq (m1 tl')) d (seq (m1 tr)) \<and> hgt (m1 result) = (1 :: int) + (if hgt (m1 tl') < hgt (m1 tr) then hgt (m1 tr) else hgt (m1 tl')) \<longrightarrow> seq (m1 result) = node_model (left1 (split'mk (seq (m1 tl')) (Some td) (seq (m1 tr)))) d (right1 (split'mk (seq (m1 tl')) (Some td) (seq (m1 tr)))) \<and> (selected s (split'mk (seq (m1 tl')) (Some td) (seq (m1 tr))) \<and> rebuild (split'mk (seq (m1 tl')) (Some td) (seq (m1 tr))) = seq (m1 t3)) \<and> hgt (m1 result) - hgt (m1 t3) \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 result) - hgt (m1 t3)))))"
  sorry
end
