import Mathlib

open Classical

namespace Lean4Why3

instance {n : Nat} : HShiftLeft (BitVec n) Int (BitVec n) where
  hShiftLeft x k := x <<< k.toNat

instance {n : Nat} : HShiftRight (BitVec n) Int (BitVec n) where
  hShiftRight x k := x >>> k.toNat

abbrev sshiftRight'i {n : ℕ} (a : BitVec n) (s : Int) : BitVec n := a.sshiftRight s.toNat

abbrev make_str_i (size : Int) := String.mk (List.replicate (Int.toNat size) 'a')
abbrev _root_.List.create_i {α} (n : ℤ) (f : ℤ -> α) := (List.range n.toNat).map f
abbrev _root_.List.create {α} (n : ℕ) (f : ℕ -> α) := (List.range n).map f

abbrev _root_.Bool.imp (a b : Bool) : Bool := !a || b

abbrev _root_.List.replicate_i {α} (n : ℤ) (x : α) := List.replicate (Int.toNat n) x

abbrev take_i {α : Type} (n : ℤ) (l : List α) := List.take n.toNat l
abbrev drop_i {α : Type} (n : ℤ) (l : List α) := List.drop n.toNat l

abbrev getElem_i! {α : Type} [Inhabited α] (l : List α) (i : Int) := l[i.toNat]!
abbrev getElem_i? {α : Type} (l : List α) (i : Int) := l[i.toNat]?

abbrev length_i {α : Type} (l : List α) := Int.ofNat l.length
abbrev slice {α : Type} (l : List α) (i j : Nat) : List α :=
  (l.drop i).take (j - i)
abbrev slice_i {α : Type} (l : List α) (i j : Int) : List α :=
  (l.drop i.toNat).take (j.toNat - i.toNat)

abbrev Sorted {α : Type} [LE α] (l : List α) := List.Sorted LE.le l
abbrev _root_.List.set_i {α : Type} (l : List α) (n : ℤ) (a : α) :=
  List.set l n.toNat a

abbrev implication (P : Prop) (Q : Prop) := P -> Q

noncomputable def map_occ {α : Type} (v : α) (m : Int -> α) (l u : Int)
  := {n | l ≤ n ∧ n < u ∧ m n = v }.ncard
noncomputable abbrev map_occ_i {α : Type} (v : α) (m : Int -> α) (l u : Int)
  := Int.ofNat (map_occ (v : α) (m : Int -> α) (l : Int) u)

abbrev _root_.BitVec.toUInt {n : Nat} (x : BitVec n) := Int.ofNat x.toNat

abbrev int'16_max : BitVec 16 := 32767
abbrev int'16_min : BitVec 16 := -32768
abbrev int'31_max : BitVec 31 := 1073741823
abbrev int'31_min : BitVec 31 := -1073741824
abbrev int'32_max : BitVec 32 := 2147483647
abbrev int'32_min : BitVec 32 := -2147483648
abbrev int'63_max : BitVec 63 := 4611686018427387903
abbrev int'63_min : BitVec 63 := -4611686018427387904
abbrev int'64_max : BitVec 64 := 9223372036854775807
abbrev int'64_min : BitVec 64 := -9223372036854775808
abbrev uint'16_max : BitVec 16 := 65535
abbrev uint'16_min : BitVec 16 := 0
abbrev uint'31_max : BitVec 31 := 2147483647
abbrev uint'31_min : BitVec 31 := 0
abbrev uint'32_max : BitVec 32 := 4294967295
abbrev uint'32_min : BitVec 32 := 0
abbrev uint'63_max : BitVec 63 := 9223372036854775807
abbrev uint'63_min : BitVec 63 := 0
abbrev uint'64_max : BitVec 64 := 18446744073709551615
abbrev uint'64_min : BitVec 64 := 0

abbrev int'16_in_bounds (x : Int) := int'16_min.toInt ≤ x ∧ x ≤ int'16_max.toInt
abbrev int'31_in_bounds (x : Int) := int'31_min.toInt ≤ x ∧ x ≤ int'31_max.toInt
abbrev int'32_in_bounds (x : Int) := int'32_min.toInt ≤ x ∧ x ≤ int'32_max.toInt
abbrev int'63_in_bounds (x : Int) := int'63_min.toInt ≤ x ∧ x ≤ int'63_max.toInt
abbrev int'64_in_bounds (x : Int) := int'64_min.toInt ≤ x ∧ x ≤ int'64_max.toInt
abbrev uint'8_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ 256
abbrev uint'16_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'16_max.toUInt
abbrev uint'31_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'31_max.toUInt
abbrev uint'32_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'32_max.toUInt
abbrev uint'63_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'63_max.toUInt
abbrev uint'64_in_bounds (x : Int) := 0 ≤ x ∧ x ≤ int'64_max.toUInt

axiom array31 : Type -> Type
axiom array32 : Type -> Type
axiom array63 : Type -> Type

axiom array31_elts : {α : Type} -> array31 α -> Int -> α
axiom array32_elts : {α : Type} -> array32 α -> Int -> α
axiom array63_elts : {α : Type} -> array63 α -> List α

noncomputable abbrev array63_nth {α : Type} [Inhabited α] (a : array63 α) (i : Int) := (array63_elts a)[i.toNat]!

axiom array31_length : {α : Type} -> array31 α -> BitVec 31
axiom array32_length : {α : Type} -> array32 α -> BitVec 32
axiom array63_length : {α : Type} -> array63 α -> BitVec 63

abbrev is_none {α : Type} (x : Option α) := x = none
abbrev is_nil {α : Type} (x : List α) := x = []

abbrev _root_.List.rev_append {α : Type} (a : List α) (b : List α) := a.reverse ++ b
abbrev _root_.Finset.is_empty {α : Type} (s : Finset α) := s = ∅
abbrev _root_.Finset.filter' {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] : Finset α
  := Finset.filter p s

abbrev _root_.Finset.card_i {α : Type} (s : Finset α) := Int.ofNat s.card

abbrev int_power (x : Int) (n : Int) := x ^ n.toNat
abbrev bv2_power (n : Int) := Int.ofNat (2 ^ n.toNat)

abbrev take_bit_i {n : Nat} (x : BitVec n) (i : Int) := x[i.toNat]!
abbrev take_bit_bv {n m : Nat} (x : BitVec n) (i : BitVec m) := x[i.toNat]!

noncomputable def _root_.Finset.pick! {α} [Inhabited α] (s : Finset α) : α :=
  if h : s.Nonempty then Classical.choose h else default
noncomputable def _root_.Set.pick! {α} [Inhabited α] (s : Finset α) : α :=
  if h : s.Nonempty then Classical.choose h else default

noncomputable abbrev _root_.BitVec.eq_sub {m : Nat} (a b : BitVec m) (i n : Nat) :=
  BitVec.extractLsb (i+n-1) i a = BitVec.extractLsb (i+n-1) i b

noncomputable abbrev _root_.BitVec.eq_sub_i {m : Nat} (a b : BitVec m) (i n : Int) :=
  BitVec.eq_sub a b i.toNat n.toNat

noncomputable abbrev _root_.BitVec.eq_sub_bv {m : Nat} {m1 : Nat} {m2 : Nat} (a b : BitVec m) (i : BitVec m1) (n : BitVec m2) :=
  BitVec.eq_sub a b i.toNat n.toNat

abbrev w8_size_bv := (8 : BitVec 8)
abbrev w16_size_bv := (16 : BitVec 16)
abbrev w32_size_bv := (32 : BitVec 32)
abbrev w64_size_bv := (64 : BitVec 64)
abbrev w128_size_bv := (128 : BitVec 128)
abbrev w256_size_bv := (256 : BitVec 256)
abbrev w8_size_i := (8 : Int)
abbrev w16_size_i := (16 : Int)
abbrev w32_size_i := (32 : Int)
abbrev w64_size_i := (64 : Int)
abbrev w128_size_i := (128 : Int)
abbrev w256_size_i := (256 : Int)

abbrev _root_.Finset.erase' {α : Type} [DecidableEq α] (a : α) (s : Finset α) : Finset α
  := Finset.erase s a

abbrev _root_.BitVec.sge {n : ℕ} (x y : BitVec n) := BitVec.sle y x
abbrev _root_.BitVec.sgt {n : ℕ} (x y : BitVec n) := BitVec.slt y x

abbrev _root_.BitVec.sshiftRight_i {n : ℕ} (x : BitVec n) (s : ℤ) := BitVec.sshiftRight x s.toNat
abbrev _root_.BitVec.sshiftRight_bv {n m : ℕ} (x : BitVec n) (s : BitVec m)
  := BitVec.sshiftRight x s.toNat

abbrev _root_.BitVec.rotateLeft_i {w : ℕ} (x : BitVec w) (n : ℤ) := BitVec.rotateLeft x n.toNat
abbrev _root_.BitVec.rotateLeft_nv {w w2 : ℕ} (x : BitVec w) (n : BitVec w2)
  := BitVec.rotateLeft x n.toNat

abbrev _root_.BitVec.rotateRight_i {w : ℕ} (x : BitVec w) (n : ℤ) := BitVec.rotateRight x n.toNat
abbrev _root_.BitVec.rotateRight_nv {w w2 : ℕ} (x : BitVec w) (n : BitVec w2)
  := BitVec.rotateRight x n.toNat

abbrev _root_.Multiset.count_i {α : Type} [DecidableEq α] (a : α) (s : Multiset α)
  := Int.ofNat (s.count a)

abbrev _root_.Multiset.card_i {α : Type} (S : Multiset α) := Int.ofNat S.card

abbrev _root_.Int.gcd_i (a : ℤ) (b : ℤ) := Int.ofNat (Int.gcd a b)

abbrev _root_.Int.Prime (p : ℤ) := Nat.Prime p.toNat
abbrev _root_.Int.Coprime (a b : ℤ) := Nat.Coprime a.toNat b.toNat

abbrev _root_.Set.remove {α : Type} (x : α) (A : Set α) := A \ {x}
abbrev _root_.Set.filter {α : Type} (S : Set α) (P : α -> Bool) := {x ∈ S | P x }

abbrev _root_.Option.the {α : Type} [Inhabited α] (opt : Option α) := opt.getD default

noncomputable abbrev _root_.Finmap.lookup! {K : Type} {V : Type} [Inhabited V] (m : Finmap (fun _ : K => V)) (k : K) :=
  (Finmap.lookup k m).getD default

noncomputable abbrev _root_.Finmap.mapsto {K V : Type} (k : K) (v : V) (m : Finmap (fun _ : K => V))
  := Finmap.lookup k m = some v

abbrev _root_.Finmap.is_empty {K V : Type} (m : Finmap (fun _ : K => V)) := m = ∅
abbrev _root_.Finmap.size {K V : Type} (m : Finmap (fun _ : K => V)) := m.keys.card

abbrev _root_.Finset.min'' {α} [Inhabited α] [LinearOrder α] (s : Finset α) : α :=
  match s.min with
  | ⊤        => default
  | .some a  => a

abbrev _root_.Finset.max'' {α} [Inhabited α] [LinearOrder α] (s : Finset α) : α :=
  match s.max with
  | ⊥        => default
  | .some a  => a

abbrev arrayExchange {α} [Inhabited α] (a1 a2 : List α) (i j : Int) : Prop :=
  let i' := i.toNat
  let j' := j.toNat
  a1 = (a2.set i' a1[j']!).set j' (a1[i']!)

abbrev _root_.List.permut_sub {α} (a1 a2 : List α) (l u : ℕ) : Prop :=
  a1.length = a2.length ∧ (0 ≤ l ∧ l ≤ a1.length) ∧ (0 ≤ u ∧ u ≤ a1.length) ∧
  List.Perm (slice a1 l u) (slice a2 l u)

abbrev _root_.List.permut_sub' {α} (a1 a2 : List α) (l u : ℕ) : Prop :=
  a1.length = a2.length ∧ slice a1 0 l = slice a2 0 l ∧
  slice a1 u a1.length = slice a2 u a1.length ∧
  List.Perm (slice a1 l u) (slice a2 l u)

abbrev _root_.List.foldr' {α β} (f : α -> β -> β) (l : List α) (x : β) := List.foldr f x l

abbrev _root_.Int.to_Real (z : ℤ) : ℝ := z

abbrev _root_.List.mem' {α} (eq : α -> α -> Bool) (x : α) (l : List α) := List.all l (eq x)

noncomputable abbrev _root_.Real.truncate (x : ℝ) : ℤ := if 0 ≤ x then Int.floor x  else Int.ceil x

alias _root_.Math.abs := abs

end Lean4Why3

open Classical
open Lean4Why3

namespace Ref
structure ref (α : Type) where
  contents : α
axiom inhabited_axiom_ref {α : Type} [Inhabited α] : Inhabited (ref α)
attribute [instance] inhabited_axiom_ref
end Ref
namespace Const
axiom const :  {β : Type} -> [Inhabited β] ->  {α : Type} -> [Inhabited α] -> β -> α -> β
axiom const'def {β : Type} {α : Type} [Inhabited β] [Inhabited α] (v : β) (x : α) : (const : β -> α -> β) v x = v
end Const
namespace MapExt
noncomputable def infix_eqeq {β : Type} {α : Type} [Inhabited β] [Inhabited α] (m1 : α -> β) (m2 : α -> β) := ∀(x : α), m1 x = m2 x
axiom extensionality {β : Type} {α : Type} [Inhabited β] [Inhabited α] (m1 : α -> β) (m2 : α -> β) (fact0 : infix_eqeq m1 m2) : m1 = m2
end MapExt
namespace Memory
axiom loc : Type
axiom inhabited_axiom_loc : Inhabited loc
attribute [instance] inhabited_axiom_loc
axiom eq : loc -> loc -> Prop
axiom eq'spec (x : loc) (y : loc) : eq x y = (x = y)
inductive kind where
  | Parent : kind
  | Left : kind
  | Right : kind
axiom inhabited_axiom_kind : Inhabited kind
attribute [instance] inhabited_axiom_kind
axiom pmem : Type
axiom inhabited_axiom_pmem : Inhabited pmem
attribute [instance] inhabited_axiom_pmem
axiom memory : Type
axiom inhabited_axiom_memory : Inhabited memory
attribute [instance] inhabited_axiom_memory
axiom accessor : memory -> kind -> loc -> loc
axiom mark : memory -> loc -> Bool
axiom null : loc
axiom non_det_magic : Type
axiom inhabited_axiom_non_det_magic : Inhabited non_det_magic
attribute [instance] inhabited_axiom_non_det_magic
axiom non_det : Type
axiom inhabited_axiom_non_det : Inhabited non_det
attribute [instance] inhabited_axiom_non_det
axiom non_det_field : non_det -> non_det_magic
end Memory
namespace Tree
inductive tree (α : Type) where
  | Empty : tree α
  | Node : tree α -> α -> tree α -> tree α
axiom inhabited_axiom_tree {α : Type} [Inhabited α] : Inhabited (tree α)
attribute [instance] inhabited_axiom_tree
noncomputable def is_empty {α : Type} [Inhabited α] (t : tree α) := match t with | (tree.Empty : tree α) => True | tree.Node _ _ _ => False
axiom is_empty'spec {α : Type} [Inhabited α] (t : tree α) : is_empty t = (t = (tree.Empty : tree α))
end Tree
namespace Size
noncomputable def size {α : Type} [Inhabited α] : Tree.tree α -> ℤ
  | (Tree.tree.Empty : Tree.tree α) => (0 : ℤ)
  | (Tree.tree.Node l x r) => (1 : ℤ) + size l + size r
axiom size_nonneg {α : Type} [Inhabited α] (t : Tree.tree α) : (0 : ℤ) ≤ size t
axiom size_empty {α : Type} [Inhabited α] (t : Tree.tree α) : ((0 : ℤ) = size t) = (t = (Tree.tree.Empty : Tree.tree α))
end Size
namespace TreeShape
axiom treel : Type
axiom inhabited_axiom_treel : Inhabited treel
attribute [instance] inhabited_axiom_treel
noncomputable def is_tree : (Memory.kind -> Memory.loc -> Memory.loc) -> Tree.tree Memory.loc -> Memory.loc -> Memory.loc -> Prop
  | memo, (Tree.tree.Empty : Tree.tree Memory.loc), c, p => c = Memory.null
  | memo, (Tree.tree.Node l m r), c, p => ¬c = Memory.null ∧ c = m ∧ memo Memory.kind.Parent c = p ∧ (let cl : Memory.loc := memo Memory.kind.Left c; let cr : Memory.loc := memo Memory.kind.Right c; (cl = Memory.null) = (cr = Memory.null) ∧ is_tree memo l cl c ∧ is_tree memo r cr c)
noncomputable def footprint : Tree.tree Memory.loc -> Set Memory.loc
  | (Tree.tree.Empty : Tree.tree Memory.loc) => (∅ : Set Memory.loc)
  | (Tree.tree.Node l m r) => Set.insert m (footprint l ∪ footprint r)
noncomputable def ext (s : Set Memory.loc) (memo1 : Memory.kind -> Memory.loc -> Memory.loc) (memo2 : Memory.kind -> Memory.loc -> Memory.loc) := ∀(k : Memory.kind) (x : Memory.loc), x ∈ s → memo1 k x = memo2 k x
noncomputable def unchanged (memo1 : Memory.kind -> Memory.loc -> Memory.loc) (memo2 : Memory.kind -> Memory.loc -> Memory.loc) := ∀(k : Memory.kind) (x : Memory.loc), memo1 k x = memo2 k x
noncomputable def was_marked (t : Tree.tree Memory.loc) (memo1 : Memory.loc -> Bool) (memo2 : Memory.loc -> Bool) := (∀(l : Memory.loc), l ∈ footprint t → memo2 l = true) ∧ (∀(l : Memory.loc), ¬l ∈ footprint t → memo2 l = memo1 l)
inductive phase where
  | GoLeft : phase
  | GoRight : phase
  | GoBack : phase
  | Finish : phase
axiom inhabited_axiom_phase : Inhabited phase
attribute [instance] inhabited_axiom_phase
noncomputable def next_phase (ph : phase) := match ph with | phase.GoLeft => phase.GoRight | phase.GoRight => phase.GoBack | phase.GoBack => phase.GoLeft | phase.Finish => phase.Finish
noncomputable def rotated (memo1 : Memory.kind -> Memory.loc -> Memory.loc) (memo2 : Memory.kind -> Memory.loc -> Memory.loc) (ph : phase) (c : Memory.loc) := (∀(k : Memory.kind) (x : Memory.loc), ¬x = c → memo1 k x = memo2 k x) ∧ (¬ph = phase.Finish → ¬c = Memory.null) ∧ (match ph with | phase.GoLeft => unchanged memo1 memo2 | phase.GoRight => memo2 Memory.kind.Left c = memo1 Memory.kind.Right c ∧ memo2 Memory.kind.Right c = memo1 Memory.kind.Parent c ∧ memo2 Memory.kind.Parent c = memo1 Memory.kind.Left c | phase.GoBack => memo1 Memory.kind.Left c = memo2 Memory.kind.Right c ∧ memo1 Memory.kind.Right c = memo2 Memory.kind.Parent c ∧ memo1 Memory.kind.Parent c = memo2 Memory.kind.Left c | phase.Finish => c = Memory.null)
end TreeShape
namespace verifythis_2016_tree_traversal_Iterative_markTreeqtvc
structure snap where
  pointers : Memory.kind -> Memory.loc -> Memory.loc
  cursor : Memory.loc
  parent : Memory.loc
  marks : Memory.loc -> Bool
axiom inhabited_axiom_snap : Inhabited snap
attribute [instance] inhabited_axiom_snap
structure frame where
  memo0 : snap
  tree : Tree.tree Memory.loc
  tleft : Tree.tree Memory.loc
  pleft : Memory.loc
  tright : Tree.tree Memory.loc
  pright : Memory.loc
  memo1 : snap
  memo2 : snap
  memo3 : snap
  memo4 : snap
axiom inhabited_axiom_frame : Inhabited frame
attribute [instance] inhabited_axiom_frame
noncomputable def frame_memo (f : frame) (pc : ℤ) := if pc ≤ (0 : ℤ) then frame.memo0 f else if pc ≤ (1 : ℤ) then frame.memo1 f else if pc ≤ (2 : ℤ) then frame.memo2 f else if pc ≤ (3 : ℤ) then frame.memo3 f else frame.memo4 f
noncomputable def bloc_rel (mem0 : Memory.kind -> Memory.loc -> Memory.loc) (ph : TreeShape.phase) (s1 : snap) (s2 : snap) := snap.parent s2 = snap.cursor s1 ∧ snap.cursor s2 = snap.pointers s2 Memory.kind.Parent (snap.parent s2) ∧ snap.marks s2 (snap.parent s2) = true ∧ (∀(l : Memory.loc), ¬l = snap.parent s2 → snap.marks s2 l = snap.marks s1 l) ∧ (if snap.pointers s1 Memory.kind.Left (snap.cursor s1) = Memory.null ∧ Memory.null = snap.pointers s1 Memory.kind.Right (snap.cursor s1) then snap.pointers s2 = snap.pointers s1 else TreeShape.rotated mem0 (snap.pointers s2) (TreeShape.next_phase ph) (snap.parent s2))
noncomputable def rec_rel (t : Tree.tree Memory.loc) (s1 : snap) (s2 : snap) := TreeShape.unchanged (snap.pointers s1) (snap.pointers s2) ∧ snap.cursor s2 = snap.parent s1 ∧ snap.parent s2 = snap.cursor s1 ∧ TreeShape.was_marked t (snap.marks s1) (snap.marks s2)
inductive stack where
  | Bottom : stack
  | Running : stack -> ℤ -> frame -> stack
  | Done : stack
axiom inhabited_axiom_stack : Inhabited stack
attribute [instance] inhabited_axiom_stack
noncomputable def is_stack : Tree.tree Memory.loc -> snap -> snap -> stack -> Option (Tree.tree Memory.loc) -> Prop
  | t, stop, scur, stack.Bottom, calls => stop = scur ∧ calls = Option.some t
  | t, stop, scur, (stack.Running s1 pc f), calls => ((0 : ℤ) ≤ pc ∧ pc ≤ (4 : ℤ)) ∧ (let m0 : snap := frame.memo0 f; is_stack t stop m0 s1 (Option.some (frame.tree f)) ∧ ¬snap.cursor m0 = Memory.null ∧ TreeShape.is_tree (snap.pointers m0) (frame.tree f) (snap.cursor m0) (snap.parent m0) ∧ frame.tree f = Tree.tree.Node (frame.tleft f) (snap.cursor m0) (frame.tright f) ∧ frame.pleft f = snap.pointers m0 Memory.kind.Left (snap.cursor m0) ∧ frame.pright f = snap.pointers m0 Memory.kind.Right (snap.cursor m0) ∧ ((1 : ℤ) ≤ pc → bloc_rel (snap.pointers m0) TreeShape.phase.GoLeft m0 (frame.memo1 f) ∧ ¬frame.pleft f = Memory.null ∧ ¬frame.pright f = Memory.null) ∧ ((2 : ℤ) ≤ pc → rec_rel (frame.tleft f) (frame.memo1 f) (frame.memo2 f)) ∧ ((3 : ℤ) ≤ pc → bloc_rel (snap.pointers m0) TreeShape.phase.GoRight (frame.memo2 f) (frame.memo3 f)) ∧ ((4 : ℤ) ≤ pc → rec_rel (frame.tright f) (frame.memo3 f) (frame.memo4 f)) ∧ frame_memo f pc = scur ∧ (match calls with | Option.none => ¬pc = (1 : ℤ) ∧ ¬pc = (3 : ℤ) | Option.some u => (if pc = (1 : ℤ) then u = frame.tleft f else pc = (3 : ℤ) ∧ u = frame.tright f)))
  | t, stop, scur, stack.Done, calls => rec_rel t stop scur ∧ calls = Option.none
noncomputable def stack_size : stack -> ℤ
  | stack.Bottom => (1 : ℤ)
  | stack.Done => (0 : ℤ)
  | (stack.Running s pc f) => stack_size s + ((100 : ℤ) - pc) + (if pc = (0 : ℤ) then (100 : ℤ) * (Size.size (frame.tleft f) + Size.size (frame.tright f)) else if pc ≤ (2 : ℤ) then (100 : ℤ) * Size.size (frame.tright f) else (0 : ℤ))
theorem markTree'vc (memo : Memory.memory) (t : Tree.tree Memory.loc) (root : Memory.loc) (fact0 : TreeShape.is_tree (Memory.accessor memo) t root Memory.null) (fact1 : ¬root = Memory.null) : let o1 : Memory.loc := Memory.null; ∀(stop : snap), snap.pointers stop = Memory.accessor memo ∧ snap.cursor stop = root ∧ snap.parent stop = o1 ∧ snap.marks stop = Memory.mark memo → (is_stack t stop stop stack.Bottom (Option.some t) ∧ TreeShape.is_tree (snap.pointers stop) t (snap.cursor stop) (snap.parent stop) ∧ ¬snap.cursor stop = Memory.null) ∧ (∀(st : stack), is_stack t stop stop st Option.none ∧ stack_size st ≤ stack_size stack.Bottom + (100 : ℤ) * Size.size t → (¬root = Memory.null ∧ snap.pointers stop = Memory.accessor memo ∧ snap.cursor stop = root ∧ snap.parent stop = o1 ∧ snap.marks stop = Memory.mark memo ∧ is_stack t stop stop st Option.none) ∧ (∀(entered : Bool) (st1 : stack) (scur : snap) (memo5 : Memory.memory), (snap.cursor scur = Memory.null → entered = true) ∧ snap.pointers scur = Memory.accessor memo5 ∧ snap.marks scur = Memory.mark memo5 ∧ is_stack t stop scur st1 Option.none → (∀(result : Bool), (if entered = true then result = (if snap.cursor scur = Memory.null then true else false) else result = false) → (result = true) = (snap.cursor scur = Memory.null)) ∧ (if ¬snap.cursor scur = Memory.null then ¬snap.cursor scur = Memory.null ∧ (∀(memo6 : Memory.memory), Memory.accessor memo6 = Memory.accessor memo5 → Memory.mark memo6 = Function.update (Memory.mark memo5) (snap.cursor scur) true → ¬snap.cursor scur = Memory.null ∧ (let o2 : Memory.loc := Memory.accessor memo6 Memory.kind.Left (snap.cursor scur); (o2 = Memory.null → ¬snap.cursor scur = Memory.null) ∧ (∀(o3 : Bool), (if o2 = Memory.null then o3 = (if Memory.accessor memo6 Memory.kind.Right (snap.cursor scur) = Memory.null then true else false) else o3 = false) → (if o3 = true then ¬snap.cursor scur = Memory.null ∧ (∀(o4 : snap), snap.pointers o4 = Memory.accessor memo6 ∧ snap.cursor o4 = Memory.accessor memo6 Memory.kind.Parent (snap.cursor scur) ∧ snap.parent o4 = snap.cursor scur ∧ snap.marks o4 = Memory.mark memo6 → (is_stack t stop scur st1 Option.none ∧ (match st1 with | stack.Bottom => False | stack.Done => False | stack.Running _ pc f => bloc_rel (snap.pointers (frame.memo0 f)) (if pc = (0 : ℤ) then TreeShape.phase.GoLeft else if pc = (2 : ℤ) then TreeShape.phase.GoRight else TreeShape.phase.GoBack) scur o4)) ∧ (∀(st2 : stack), is_stack t stop o4 st2 Option.none ∧ stack_size st2 < stack_size st1 → ((0 : ℤ) ≤ stack_size st1 ∧ stack_size st2 < stack_size st1) ∧ (Memory.accessor memo6 Memory.kind.Parent (snap.cursor scur) = Memory.null → True) ∧ snap.pointers o4 = Memory.accessor memo6 ∧ snap.cursor o4 = Memory.accessor memo6 Memory.kind.Parent (snap.cursor scur) ∧ snap.parent o4 = snap.cursor scur ∧ snap.marks o4 = Memory.mark memo6 ∧ is_stack t stop o4 st2 Option.none)) else ¬snap.cursor scur = Memory.null ∧ ¬snap.cursor scur = Memory.null ∧ (let o4 : Memory.kind := Memory.kind.Left; ¬snap.cursor scur = Memory.null ∧ (∀(memo7 : Memory.memory), Memory.mark memo7 = Memory.mark memo6 → Memory.accessor memo7 = Function.update (Memory.accessor memo6) o4 (Function.update (Memory.accessor memo6 o4) (snap.cursor scur) (Memory.accessor memo6 Memory.kind.Right (snap.cursor scur))) → ¬snap.cursor scur = Memory.null ∧ (let o5 : Memory.kind := Memory.kind.Right; ¬snap.cursor scur = Memory.null ∧ (∀(memo8 : Memory.memory), Memory.mark memo8 = Memory.mark memo7 → Memory.accessor memo8 = Function.update (Memory.accessor memo7) o5 (Function.update (Memory.accessor memo7 o5) (snap.cursor scur) (Memory.accessor memo7 Memory.kind.Parent (snap.cursor scur))) → (let o6 : Memory.kind := Memory.kind.Parent; ¬snap.cursor scur = Memory.null ∧ (∀(memo9 : Memory.memory), Memory.mark memo9 = Memory.mark memo8 → Memory.accessor memo9 = Function.update (Memory.accessor memo8) o6 (Function.update (Memory.accessor memo8 o6) (snap.cursor scur) (Memory.accessor memo6 Memory.kind.Left (snap.cursor scur))) → (∀(o7 : snap), snap.pointers o7 = Memory.accessor memo9 ∧ snap.cursor o7 = Memory.accessor memo6 Memory.kind.Left (snap.cursor scur) ∧ snap.parent o7 = snap.cursor scur ∧ snap.marks o7 = Memory.mark memo9 → (is_stack t stop scur st1 Option.none ∧ (match st1 with | stack.Bottom => False | stack.Done => False | stack.Running _ pc f => bloc_rel (snap.pointers (frame.memo0 f)) (if pc = (0 : ℤ) then TreeShape.phase.GoLeft else if pc = (2 : ℤ) then TreeShape.phase.GoRight else TreeShape.phase.GoBack) scur o7)) ∧ (∀(st2 : stack), is_stack t stop o7 st2 Option.none ∧ stack_size st2 < stack_size st1 → ((0 : ℤ) ≤ stack_size st1 ∧ stack_size st2 < stack_size st1) ∧ (Memory.accessor memo6 Memory.kind.Left (snap.cursor scur) = Memory.null → True) ∧ snap.pointers o7 = Memory.accessor memo9 ∧ snap.cursor o7 = Memory.accessor memo6 Memory.kind.Left (snap.cursor scur) ∧ snap.parent o7 = snap.cursor scur ∧ snap.marks o7 = Memory.mark memo9 ∧ is_stack t stop o7 st2 Option.none)))))))))))) else (match st1 with | stack.Done => True | _ => False) ∧ ((match st1 with | stack.Done => True | _ => False) → (let o2 : Memory.loc := Memory.null; let o3 : Memory.kind -> Memory.loc -> Memory.loc := snap.pointers stop; (TreeShape.ext (TreeShape.footprint t) o3 (Memory.accessor memo5) ∧ TreeShape.is_tree o3 t root o2) ∧ (TreeShape.is_tree (Memory.accessor memo5) t root o2 → TreeShape.is_tree (Memory.accessor memo5) t root Memory.null ∧ TreeShape.unchanged (Memory.accessor memo) (Memory.accessor memo5) ∧ TreeShape.was_marked t (Memory.mark memo) (Memory.mark memo5)))))))
  := sorry
end verifythis_2016_tree_traversal_Iterative_markTreeqtvc
