theory priority_queue_PQueue_extract_minqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "../../lib/isabelle/avl_SelectionTypes"
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
definition op :: "t1 option \<Rightarrow> t1 option \<Rightarrow> t1 option"
  where "op x y = (case x of None \<Rightarrow> y | Some a \<Rightarrow> (case y of None \<Rightarrow> x | Some b \<Rightarrow> (if lt b a then y else x)))" for x y
axiomatization where assoc:   "op a (op b c) = op (op a b) c"
  for a :: "t1 option"
  and b :: "t1 option"
  and c :: "t1 option"
axiomatization where neutral'0:   "op x None = x"
  for x :: "t1 option"
axiomatization where neutral'1:   "x = op None x"
  for x :: "t1 option"
consts agg :: "('a \<Rightarrow> t1 option) \<Rightarrow> 'a list \<Rightarrow> t1 option"
axiomatization where agg'def:   "if int (length s) = (0 :: int) then agg f s = None else agg f s = op (f (s ! (0 :: nat))) (agg f (drop (1 :: nat) s))"
  for s :: "'a list"
  and f :: "'a \<Rightarrow> t1 option"
definition measure :: "'a t \<Rightarrow> t1 option"
  where "measure d = Some (key d)" for d
typedecl  selector
definition selection_possible :: "'e \<Rightarrow> 'g list \<Rightarrow> _"
  where "selection_possible x s \<longleftrightarrow> \<not>int (length s) = (0 :: int)" for x s
definition lower_bound :: "t1 \<Rightarrow> 'a t list \<Rightarrow> _"
  where "lower_bound x s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> le x (key (s ! nat i)))" for x s
definition lower_bound_strict :: "t1 \<Rightarrow> 'a t list \<Rightarrow> _"
  where "lower_bound_strict x s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> lt x (key (s ! nat i)))" for x s
definition selected :: "'e \<Rightarrow> 'a t split \<Rightarrow> _"
  where "selected x e \<longleftrightarrow> (case middle e of (None :: 'a t option) \<Rightarrow> False | Some d \<Rightarrow> lower_bound (key d) (right1 e) \<and> lower_bound_strict (key d) (left1 e))" for x e
datatype 'a tree = Empty | Node "'a tree" "'a t" "'a tree" "nat" "t1 option"
datatype 'a m = m'mk (seq: "'a t list") (hgt: "int")
definition node_model :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "node_model l d r = l @ Cons d r" for l d r
fun seq_model :: "'a tree \<Rightarrow> 'a t list"
  where "seq_model (Empty :: 'a tree) = ([] :: 'a t list)"
      | "seq_model (Node l d r x x0) = node_model (seq_model l) d (seq_model r)" for l d r x x0
fun real_height :: "'a tree \<Rightarrow> int"
  where "real_height (Empty :: 'a tree) = (0 :: int)"
      | "real_height (Node l x r x0 x1) = (let hl :: int = real_height l; hr :: int = real_height r in (1 :: int) + (if hl < hr then hr else hl))" for l x r x0 x1
consts measure_closure :: "'a t \<Rightarrow> t1 option"
axiomatization where measure_closure_def:   "measure_closure y = measure y"
  for y :: "'a t"
fun balanced :: "'a tree \<Rightarrow> _"
  where "balanced (Empty :: 'a tree) = True"
      | "balanced (Node l x r h m1) = (int h = real_height (Node l x r h m1) \<and> m1 = agg measure_closure (seq_model (Node l x r h m1)) \<and> (-int balancing \<le> real_height r - real_height l \<and> real_height r - real_height l \<le> int balancing) \<and> balanced l \<and> balanced r)" for l x r h m1
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
datatype 'a view = AEmpty | ANode "'a t3" "'a t" "'a t3" "nat" "t1 option"
typedecl  part
typedecl 'a t4
datatype 'a m2 = m'mk1 (bag: "'a t \<Rightarrow> int") (minimum: "'a t") (card: "int")
consts to_bag :: "'a list \<Rightarrow> 'a \<Rightarrow> int"
axiomatization where to_bag'def:   "to_bag s x = int (count_list (drop (0 :: nat) (take (length s - (0 :: nat)) s)) x)"
  for s :: "'a list"
  and x :: "'a"
consts get_minimum_index :: "'a t list \<Rightarrow> int"
axiomatization where get_minimum_index'spec'2'0:   "(0 :: int) \<le> get_minimum_index s"
 if "\<not>int (length s) = (0 :: int)"
  for s :: "'a t list"
axiomatization where get_minimum_index'spec'2'1:   "get_minimum_index s < int (length s)"
 if "\<not>int (length s) = (0 :: int)"
  for s :: "'a t list"
axiomatization where get_minimum_index'spec'1:   "agg measure_closure s = Some (key (s ! nat (get_minimum_index s)))"
 if "\<not>int (length s) = (0 :: int)"
  for s :: "'a t list"
axiomatization where get_minimum_index'spec'0:   "lower_bound_strict (key (s ! nat (get_minimum_index s))) (take (nat (get_minimum_index s)) s)"
 if "\<not>int (length s) = (0 :: int)"
  for s :: "'a t list"
axiomatization where get_minimum_index'spec:   "lower_bound (key (s ! nat (get_minimum_index s))) (drop (nat (get_minimum_index s)) s)"
 if "\<not>int (length s) = (0 :: int)"
  for s :: "'a t list"
definition m3 :: "'a t3 \<Rightarrow> 'a m2"
  where "m3 t5 = (m'mk1 :: ('a t \<Rightarrow> int) \<Rightarrow> 'a t \<Rightarrow> int \<Rightarrow> 'a m2) (to_bag (seq (m1 t5))) (seq (m1 t5) ! nat (get_minimum_index (seq (m1 t5)))) (int (length (seq (m1 t5))))" for t5
theorem extract_min'vc:
  fixes t5 :: "'a t3"
  fixes o1 :: "bool"
  assumes fact0: "int (length (seq (m1 t5))) = (0 :: int) \<longrightarrow> o1 = True"
  assumes fact1: "o1 = True \<longrightarrow> seq (m1 t5) = ([] :: 'a t list)"
  shows "if o1 = True then card (m3 t5) = (0 :: int) \<and> (\<forall>(d :: 'a t). bag (m3 t5) d = (0 :: int)) else selection_possible () (seq (m1 t5)) \<and> (\<forall>(o2 :: 'a t split) (o3 :: 'a t option) (e :: 'a t3). (selected () o2 \<and> rebuild o2 = seq (m1 t5)) \<and> seq (m1 e) = left1 o2 @ right1 o2 \<and> (hgt (m1 t5) - hgt (m1 e) \<le> (1 :: int) \<and> (0 :: int) \<le> hgt (m1 t5) - hgt (m1 e)) \<and> (case o3 of (None :: 'a t option) \<Rightarrow> middle o2 = (None :: 'a t option) | Some d2 \<Rightarrow> middle o2 = Some d2) \<longrightarrow> (case o3 of (None :: 'a t option) \<Rightarrow> False | Some d \<Rightarrow> True) \<and> (\<forall>(result :: ('a t \<times> 'a t3) option). (case o3 of (None :: 'a t option) \<Rightarrow> False | Some d \<Rightarrow> result = Some (d, e)) \<longrightarrow> (case result of (None :: ('a t \<times> 'a t3) option) \<Rightarrow> card (m3 t5) = (0 :: int) \<and> (\<forall>(d :: 'a t). bag (m3 t5) d = (0 :: int)) | Some (d, e1) \<Rightarrow> card (m3 t5) = card (m3 e1) + (1 :: int) \<and> bag (m3 t5) d = bag (m3 e1) d + (1 :: int) \<and> d = minimum (m3 t5) \<and> (\<forall>(d2 :: 'a t). \<not>d2 = d \<longrightarrow> bag (m3 t5) d2 = bag (m3 e1) d2))))"
  sorry
end
