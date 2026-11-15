theory priority_queue_PQueue_selected_partqtvc
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
consts measure_closure :: "'a t \<Rightarrow> t1 option"
axiomatization where measure_closure_def:   "measure_closure y = measure y"
  for y :: "'a t"
theorem selected_part'vc:
  fixes d :: "'a t"
  fixes rseq :: "'a t list"
  fixes lseq :: "'a t list"
  shows "let s :: unit = (); kd :: t1 = key d in (case agg measure_closure rseq of None \<Rightarrow> (case agg measure_closure lseq of None \<Rightarrow> True | Some x \<Rightarrow> True) | Some x \<Rightarrow> (case agg measure_closure lseq of None \<Rightarrow> True | Some x1 \<Rightarrow> True)) \<and> (\<forall>(result :: unit part_base). (case agg measure_closure rseq of None \<Rightarrow> (case agg measure_closure lseq of None \<Rightarrow> result = Here | Some x \<Rightarrow> (\<exists>(o1 :: int). (((0 :: int) < o1 \<longleftrightarrow> lt x kd) \<and> (o1 < (0 :: int) \<longleftrightarrow> lt kd x) \<and> (o1 = (0 :: int) \<longleftrightarrow> eq kd x)) \<and> (if o1 < (0 :: int) then result = Here else result = Left ()))) | Some x \<Rightarrow> (case agg measure_closure lseq of None \<Rightarrow> (\<exists>(o1 :: int). (((0 :: int) < o1 \<longleftrightarrow> lt x kd) \<and> (o1 < (0 :: int) \<longleftrightarrow> lt kd x) \<and> (o1 = (0 :: int) \<longleftrightarrow> eq kd x)) \<and> (if o1 \<le> (0 :: int) then result = Here else result = Right ())) | Some x1 \<Rightarrow> (\<exists>(o1 :: int). (((0 :: int) < o1 \<longleftrightarrow> lt x kd) \<and> (o1 < (0 :: int) \<longleftrightarrow> lt kd x) \<and> (o1 = (0 :: int) \<longleftrightarrow> eq kd x)) \<and> (if o1 \<le> (0 :: int) then \<exists>(o2 :: int). (((0 :: int) < o2 \<longleftrightarrow> lt kd x1) \<and> (o2 < (0 :: int) \<longleftrightarrow> lt x1 kd) \<and> (o2 = (0 :: int) \<longleftrightarrow> eq x1 kd)) \<and> (if o2 \<le> (0 :: int) then result = Left () else result = Here) else \<exists>(o2 :: int). (((0 :: int) < o2 \<longleftrightarrow> lt x x1) \<and> (o2 < (0 :: int) \<longleftrightarrow> lt x1 x) \<and> (o2 = (0 :: int) \<longleftrightarrow> eq x1 x)) \<and> (if o2 \<le> (0 :: int) then result = Left () else result = Right ()))))) \<longrightarrow> (case result of Here \<Rightarrow> selected s (split'mk lseq (Some d) rseq) | Left rsl \<Rightarrow> selection_possible rsl lseq \<and> (\<forall>(e :: 'a t split). selected rsl e \<and> rebuild e = lseq \<longrightarrow> selected s (right_extend e d rseq)) | Right rsr \<Rightarrow> selection_possible rsr rseq \<and> (\<forall>(e :: 'a t split). selected rsr e \<and> rebuild e = rseq \<longrightarrow> selected s (left_extend lseq d e))))"
  sorry
end
