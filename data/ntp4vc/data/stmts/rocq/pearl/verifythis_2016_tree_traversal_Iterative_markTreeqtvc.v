From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import Why3.why3.Ref.Ref.
Require Import Why3.map.Const.
Require Import Why3.map.MapExt.
Require Import verifythis_2016_tree_traversal_vcg.verifythis_2016_tree_traversal.Memory.
Require Import verifythis_2016_tree_traversal_vcg.verifythis_2016_tree_traversal.TreeShape.
Require Import Why3.bintree.Tree.
Require Import Why3.bintree.Size.
Open Scope Z_scope.
Inductive snap :=
  | snap'mk : (kind -> loc -> loc) -> loc -> loc -> (loc -> bool) -> snap.
Axiom snap_inhabited : Inhabited snap.
Global Existing Instance snap_inhabited.
Axiom snap_countable : Countable snap.
Global Existing Instance snap_countable.
Definition pointers (x : snap) := match x with |  snap'mk a _ _ _ => a end.
Definition cursor (x : snap) := match x with |  snap'mk _ a _ _ => a end.
Definition parent (x : snap) := match x with |  snap'mk _ _ a _ => a end.
Definition marks (x : snap) := match x with |  snap'mk _ _ _ a => a end.
Inductive frame :=
  | frame'mk : snap -> tree loc -> tree loc -> loc -> tree loc -> loc -> snap -> snap -> snap -> snap -> frame.
Axiom frame_inhabited : Inhabited frame.
Global Existing Instance frame_inhabited.
Axiom frame_countable : Countable frame.
Global Existing Instance frame_countable.
Definition memo0 (x : frame) := match x with |  frame'mk a _ _ _ _ _ _ _ _ _ => a end.
Definition tree (x : frame) := match x with |  frame'mk _ a _ _ _ _ _ _ _ _ => a end.
Definition tleft (x : frame) := match x with |  frame'mk _ _ a _ _ _ _ _ _ _ => a end.
Definition pleft (x : frame) := match x with |  frame'mk _ _ _ a _ _ _ _ _ _ => a end.
Definition tright (x : frame) := match x with |  frame'mk _ _ _ _ a _ _ _ _ _ => a end.
Definition pright (x : frame) := match x with |  frame'mk _ _ _ _ _ a _ _ _ _ => a end.
Definition memo1 (x : frame) := match x with |  frame'mk _ _ _ _ _ _ a _ _ _ => a end.
Definition memo2 (x : frame) := match x with |  frame'mk _ _ _ _ _ _ _ a _ _ => a end.
Definition memo3 (x : frame) := match x with |  frame'mk _ _ _ _ _ _ _ _ a _ => a end.
Definition memo4 (x : frame) := match x with |  frame'mk _ _ _ _ _ _ _ _ _ a => a end.
Definition frame_memo (f : frame) (pc : Z) : snap := if decide (pc ≤ 0%Z) then memo0 f else if decide (pc ≤ 1%Z) then memo1 f else if decide (pc ≤ 2%Z) then memo2 f else if decide (pc ≤ 3%Z) then memo3 f else memo4 f.
Definition bloc_rel (mem0 : kind -> loc -> loc) (ph : phase) (s1 : snap) (s2 : snap) := parent s2 = cursor s1 ∧ cursor s2 = pointers s2 Parent (parent s2) ∧ marks s2 (parent s2) = true ∧ (∀(l : loc), ¬ l = parent s2 -> marks s2 l = marks s1 l) ∧ (if decide (pointers s1 Left (cursor s1) = null ∧ null = pointers s1 Right (cursor s1)) then pointers s2 = pointers s1 else rotated mem0 (pointers s2) (next_phase ph) (parent s2)).
Definition rec_rel (t : Tree.tree loc) (s1 : snap) (s2 : snap) := unchanged (pointers s1) (pointers s2) ∧ cursor s2 = parent s1 ∧ parent s2 = cursor s1 ∧ was_marked t (marks s1) (marks s2).
Inductive stack :=
  | Bottom : stack
  | Running : stack -> Z -> frame -> stack
  | Done : stack.
Axiom stack_inhabited : Inhabited stack.
Global Existing Instance stack_inhabited.
Axiom stack_countable : Countable stack.
Global Existing Instance stack_countable.
Program Fixpoint is_stack (t : Tree.tree loc) (stop : snap) (scur : snap) (s : stack) (calls : option (Tree.tree loc)) : Prop :=
match s with | Bottom => stop = scur ∧ calls = Some t | Running s1 pc f => (0%Z ≤ pc ∧ pc ≤ 4%Z) ∧ (let m0 : snap := memo0 f in is_stack t stop m0 s1 (Some (tree f)) ∧ ¬ cursor m0 = null ∧ is_tree (pointers m0) (tree f) (cursor m0) (parent m0) ∧ tree f = Node (tleft f) (cursor m0) (tright f) ∧ pleft f = pointers m0 Left (cursor m0) ∧ pright f = pointers m0 Right (cursor m0) ∧ (1%Z ≤ pc -> bloc_rel (pointers m0) GoLeft m0 (memo1 f) ∧ ¬ pleft f = null ∧ ¬ pright f = null) ∧ (2%Z ≤ pc -> rec_rel (tleft f) (memo1 f) (memo2 f)) ∧ (3%Z ≤ pc -> bloc_rel (pointers m0) GoRight (memo2 f) (memo3 f)) ∧ (4%Z ≤ pc -> rec_rel (tright f) (memo3 f) (memo4 f)) ∧ frame_memo f pc = scur ∧ (match calls with | None => ¬ pc = 1%Z ∧ ¬ pc = 3%Z | Some u => (if decide (pc = 1%Z) then u = tleft f else pc = 3%Z ∧ u = tright f) end)) | Done => rec_rel t stop scur ∧ calls = None end.
Admit Obligations.
Program Fixpoint stack_size (st : stack) : Z :=
match st with | Bottom => 1%Z | Done => 0%Z | Running s pc f => stack_size s + (100%Z - pc) + (if decide (pc = 0%Z) then 100%Z * (Size.size (tleft f) + Size.size (tright f)) else if decide (pc ≤ 2%Z) then 100%Z * Size.size (tright f) else 0%Z) end.
Admit Obligations.
Theorem markTree'vc (memo : memory) (t : Tree.tree loc) (root : loc) (fact0 : is_tree (accessor memo) t root null) (fact1 : ¬ root = null) : let o1 : loc := null in ∀(stop : snap), pointers stop = accessor memo ∧ cursor stop = root ∧ parent stop = o1 ∧ marks stop = mark memo -> (is_stack t stop stop Bottom (Some t) ∧ is_tree (pointers stop) t (cursor stop) (parent stop) ∧ ¬ cursor stop = null) ∧ (∀(st : stack), is_stack t stop stop st None ∧ stack_size st ≤ stack_size Bottom + 100%Z * Size.size t -> (¬ root = null ∧ pointers stop = accessor memo ∧ cursor stop = root ∧ parent stop = o1 ∧ marks stop = mark memo ∧ is_stack t stop stop st None) ∧ (∀(entered : bool) (st1 : stack) (scur : snap) (memo5 : memory), (cursor scur = null -> entered = true) ∧ pointers scur = accessor memo5 ∧ marks scur = mark memo5 ∧ is_stack t stop scur st1 None -> (∀(result : bool), (if decide (entered = true) then result = (if decide (cursor scur = null) then true else false) else result = false) -> (result = true) = (cursor scur = null)) ∧ (if decide (¬ cursor scur = null) then ¬ cursor scur = null ∧ (∀(memo6 : memory), accessor memo6 = accessor memo5 -> mark memo6 = fun_updt (mark memo5) (cursor scur) true -> ¬ cursor scur = null ∧ (let o2 : loc := accessor memo6 Left (cursor scur) in (o2 = null -> ¬ cursor scur = null) ∧ (∀(o3 : bool), (if decide (o2 = null) then o3 = (if decide (accessor memo6 Right (cursor scur) = null) then true else false) else o3 = false) -> (if decide (o3 = true) then ¬ cursor scur = null ∧ (∀(o4 : snap), pointers o4 = accessor memo6 ∧ cursor o4 = accessor memo6 Parent (cursor scur) ∧ parent o4 = cursor scur ∧ marks o4 = mark memo6 -> (is_stack t stop scur st1 None ∧ (match st1 with | Bottom => False | Done => False | Running _ pc f => bloc_rel (pointers (memo0 f)) (if decide (pc = 0%Z) then GoLeft else if decide (pc = 2%Z) then GoRight else GoBack) scur o4 end)) ∧ (∀(st2 : stack), is_stack t stop o4 st2 None ∧ stack_size st2 < stack_size st1 -> (0%Z ≤ stack_size st1 ∧ stack_size st2 < stack_size st1) ∧ (accessor memo6 Parent (cursor scur) = null -> True) ∧ pointers o4 = accessor memo6 ∧ cursor o4 = accessor memo6 Parent (cursor scur) ∧ parent o4 = cursor scur ∧ marks o4 = mark memo6 ∧ is_stack t stop o4 st2 None)) else ¬ cursor scur = null ∧ ¬ cursor scur = null ∧ (let o4 : kind := Left in ¬ cursor scur = null ∧ (∀(memo7 : memory), mark memo7 = mark memo6 -> accessor memo7 = fun_updt (accessor memo6) o4 (fun_updt (accessor memo6 o4) (cursor scur) (accessor memo6 Right (cursor scur))) -> ¬ cursor scur = null ∧ (let o5 : kind := Right in ¬ cursor scur = null ∧ (∀(memo8 : memory), mark memo8 = mark memo7 -> accessor memo8 = fun_updt (accessor memo7) o5 (fun_updt (accessor memo7 o5) (cursor scur) (accessor memo7 Parent (cursor scur))) -> (let o6 : kind := Parent in ¬ cursor scur = null ∧ (∀(memo9 : memory), mark memo9 = mark memo8 -> accessor memo9 = fun_updt (accessor memo8) o6 (fun_updt (accessor memo8 o6) (cursor scur) (accessor memo6 Left (cursor scur))) -> (∀(o7 : snap), pointers o7 = accessor memo9 ∧ cursor o7 = accessor memo6 Left (cursor scur) ∧ parent o7 = cursor scur ∧ marks o7 = mark memo9 -> (is_stack t stop scur st1 None ∧ (match st1 with | Bottom => False | Done => False | Running _ pc f => bloc_rel (pointers (memo0 f)) (if decide (pc = 0%Z) then GoLeft else if decide (pc = 2%Z) then GoRight else GoBack) scur o7 end)) ∧ (∀(st2 : stack), is_stack t stop o7 st2 None ∧ stack_size st2 < stack_size st1 -> (0%Z ≤ stack_size st1 ∧ stack_size st2 < stack_size st1) ∧ (accessor memo6 Left (cursor scur) = null -> True) ∧ pointers o7 = accessor memo9 ∧ cursor o7 = accessor memo6 Left (cursor scur) ∧ parent o7 = cursor scur ∧ marks o7 = mark memo9 ∧ is_stack t stop o7 st2 None)))))))))))) else (match st1 with | Done => True | _ => False end) ∧ ((match st1 with | Done => True | _ => False end) -> (let o2 : loc := null in let o3 : kind -> loc -> loc := pointers stop in (ext (footprint t) o3 (accessor memo5) ∧ is_tree o3 t root o2) ∧ (is_tree (accessor memo5) t root o2 -> is_tree (accessor memo5) t root null ∧ unchanged (accessor memo) (accessor memo5) ∧ was_marked t (mark memo) (mark memo5))))))).
Admitted.
