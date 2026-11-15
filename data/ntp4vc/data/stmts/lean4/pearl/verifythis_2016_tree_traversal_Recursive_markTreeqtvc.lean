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
namespace verifythis_2016_tree_traversal_Recursive_markTreeqtvc
theorem markTree'vc (memo : Memory.memory) (t : Tree.tree Memory.loc) (root : Memory.loc) (fact0 : TreeShape.is_tree (Memory.accessor memo) t root Memory.null) (fact1 : ¬root = Memory.null) : let o1 : Memory.loc := Memory.null; (∀(entered : Bool) (x : Memory.loc) (memo1 : Memory.memory) (mem0 : Memory.kind -> Memory.loc -> Memory.loc) (ph : TreeShape.phase), TreeShape.rotated mem0 (Memory.accessor memo1) ph x ∧ (ph = TreeShape.phase.Finish → entered = true) → (∀(o2 : Bool), (if entered = true then o2 = (if x = Memory.null then true else false) else o2 = false) → (if o2 = true then ph = TreeShape.phase.Finish else ¬x = Memory.null ∧ (∀(memo2 : Memory.memory), Memory.accessor memo2 = Memory.accessor memo1 → Memory.mark memo2 = Function.update (Memory.mark memo1) x true → ¬x = Memory.null ∧ (let o3 : Memory.loc := Memory.accessor memo2 Memory.kind.Left x; (o3 = Memory.null → ¬x = Memory.null) ∧ (∀(o4 : Bool), (if o3 = Memory.null then o4 = (if Memory.accessor memo2 Memory.kind.Right x = Memory.null then true else false) else o4 = false) → (if o4 = true then ¬x = Memory.null ∧ ¬ph = TreeShape.phase.Finish ∧ Memory.mark memo2 x = true ∧ (∀(l : Memory.loc), ¬l = x → Memory.mark memo2 l = Memory.mark memo1 l) ∧ (if Memory.accessor memo1 Memory.kind.Left x = Memory.null ∧ Memory.null = Memory.accessor memo1 Memory.kind.Right x then Memory.accessor memo2 = Memory.accessor memo1 else TreeShape.rotated mem0 (Memory.accessor memo2) (TreeShape.next_phase ph) x) else ¬x = Memory.null ∧ ¬x = Memory.null ∧ (let o5 : Memory.kind := Memory.kind.Left; ¬x = Memory.null ∧ (∀(memo3 : Memory.memory), Memory.mark memo3 = Memory.mark memo2 → Memory.accessor memo3 = Function.update (Memory.accessor memo2) o5 (Function.update (Memory.accessor memo2 o5) x (Memory.accessor memo2 Memory.kind.Right x)) → ¬x = Memory.null ∧ (let o6 : Memory.kind := Memory.kind.Right; ¬x = Memory.null ∧ (∀(memo4 : Memory.memory), Memory.mark memo4 = Memory.mark memo3 → Memory.accessor memo4 = Function.update (Memory.accessor memo3) o6 (Function.update (Memory.accessor memo3 o6) x (Memory.accessor memo3 Memory.kind.Parent x)) → (let o7 : Memory.kind := Memory.kind.Parent; ¬x = Memory.null ∧ (∀(memo5 : Memory.memory), Memory.mark memo5 = Memory.mark memo4 → Memory.accessor memo5 = Function.update (Memory.accessor memo4) o7 (Function.update (Memory.accessor memo4 o7) x (Memory.accessor memo2 Memory.kind.Left x)) → Memory.accessor memo2 Memory.kind.Left x = Memory.accessor memo5 Memory.kind.Parent x ∧ ¬ph = TreeShape.phase.Finish ∧ Memory.mark memo5 x = true ∧ (∀(l : Memory.loc), ¬l = x → Memory.mark memo5 l = Memory.mark memo1 l) ∧ (if Memory.accessor memo1 Memory.kind.Left x = Memory.null ∧ Memory.null = Memory.accessor memo1 Memory.kind.Right x then Memory.accessor memo5 = Memory.accessor memo1 else TreeShape.rotated mem0 (Memory.accessor memo5) (TreeShape.next_phase ph) x)))))))))))))) ∧ (∀(z : Memory.loc) (x : Memory.loc) (memo1 : Memory.memory) (t1 : Tree.tree Memory.loc), ¬x = Memory.null ∧ TreeShape.is_tree (Memory.accessor memo1) t1 x z → (let mem0 : Memory.kind -> Memory.loc -> Memory.loc := Memory.accessor memo1; ¬x = Memory.null ∧ (let x_lf : Memory.loc := Memory.accessor memo1 Memory.kind.Left x; ¬x = Memory.null ∧ (let x_rg : Memory.loc := Memory.accessor memo1 Memory.kind.Right x; (match t1 with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node l _ r => True) ∧ (∀(lf : Tree.tree Memory.loc) (rg : Tree.tree Memory.loc), (match t1 with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node l _ r => lf = l ∧ rg = r) → TreeShape.is_tree mem0 (Tree.tree.Node lf x rg) x z ∧ (¬x ∈ TreeShape.footprint lf ∧ ¬x ∈ TreeShape.footprint rg → (let o2 : TreeShape.phase := TreeShape.phase.GoLeft; TreeShape.rotated mem0 (Memory.accessor memo1) o2 x ∧ (∀(memo2 : Memory.memory), Memory.mark memo2 x = true ∧ (∀(l : Memory.loc), ¬l = x → Memory.mark memo2 l = Memory.mark memo1 l) ∧ (if Memory.accessor memo1 Memory.kind.Left x = Memory.null ∧ Memory.null = Memory.accessor memo1 Memory.kind.Right x then Memory.accessor memo2 = Memory.accessor memo1 else TreeShape.rotated mem0 (Memory.accessor memo2) (TreeShape.next_phase o2) x) → (∀(result : Bool), (if x_lf = Memory.null then result = (if x_rg = Memory.null then true else false) else result = false) → (result = true) = (x_lf = Memory.null ∧ x_rg = Memory.null) ∧ (result = true → lf = (Tree.tree.Empty : Tree.tree Memory.loc) ∧ rg = (Tree.tree.Empty : Tree.tree Memory.loc))) ∧ ((x_lf = Memory.null ∧ x_rg = Memory.null → lf = (Tree.tree.Empty : Tree.tree Memory.loc) ∧ rg = (Tree.tree.Empty : Tree.tree Memory.loc)) → (if ¬(x_lf = Memory.null ∧ x_rg = Memory.null) then (TreeShape.ext (TreeShape.footprint lf) mem0 (Memory.accessor memo2) ∧ TreeShape.is_tree mem0 lf x_lf x) ∧ (TreeShape.is_tree (Memory.accessor memo2) lf x_lf x → ((match t1 with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node f _ f1 => f = lf ∨ f1 = lf) ∧ ¬Memory.accessor memo2 Memory.kind.Parent x = Memory.null ∧ TreeShape.is_tree (Memory.accessor memo2) lf (Memory.accessor memo2 Memory.kind.Parent x) x) ∧ (∀(memo3 : Memory.memory), TreeShape.unchanged (Memory.accessor memo2) (Memory.accessor memo3) ∧ TreeShape.was_marked lf (Memory.mark memo2) (Memory.mark memo3) → (let o3 : TreeShape.phase := TreeShape.phase.GoRight; TreeShape.rotated mem0 (Memory.accessor memo3) o3 x ∧ (∀(memo4 : Memory.memory), Memory.mark memo4 x = true ∧ (∀(l : Memory.loc), ¬l = x → Memory.mark memo4 l = Memory.mark memo3 l) ∧ (if Memory.accessor memo3 Memory.kind.Left x = Memory.null ∧ Memory.null = Memory.accessor memo3 Memory.kind.Right x then Memory.accessor memo4 = Memory.accessor memo3 else TreeShape.rotated mem0 (Memory.accessor memo4) (TreeShape.next_phase o3) x) → (TreeShape.ext (TreeShape.footprint rg) mem0 (Memory.accessor memo4) ∧ TreeShape.is_tree mem0 rg x_rg x) ∧ (TreeShape.is_tree (Memory.accessor memo4) rg x_rg x → ((match t1 with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node f _ f1 => f = rg ∨ f1 = rg) ∧ ¬Memory.accessor memo4 Memory.kind.Parent x = Memory.null ∧ TreeShape.is_tree (Memory.accessor memo4) rg (Memory.accessor memo4 Memory.kind.Parent x) x) ∧ (∀(memo5 : Memory.memory), TreeShape.unchanged (Memory.accessor memo4) (Memory.accessor memo5) ∧ TreeShape.was_marked rg (Memory.mark memo4) (Memory.mark memo5) → (let o4 : TreeShape.phase := TreeShape.phase.GoBack; TreeShape.rotated mem0 (Memory.accessor memo5) o4 x ∧ (∀(memo6 : Memory.memory), Memory.mark memo6 x = true ∧ (∀(l : Memory.loc), ¬l = x → Memory.mark memo6 l = Memory.mark memo5 l) ∧ (if Memory.accessor memo5 Memory.kind.Left x = Memory.null ∧ Memory.null = Memory.accessor memo5 Memory.kind.Right x then Memory.accessor memo6 = Memory.accessor memo5 else TreeShape.rotated mem0 (Memory.accessor memo6) (TreeShape.next_phase o4) x) → TreeShape.unchanged (Memory.accessor memo1) (Memory.accessor memo6) ∧ Memory.accessor memo6 Memory.kind.Parent x = z ∧ TreeShape.was_marked t1 (Memory.mark memo1) (Memory.mark memo6))))))))) else TreeShape.unchanged (Memory.accessor memo1) (Memory.accessor memo2) ∧ Memory.accessor memo2 Memory.kind.Parent x = z ∧ TreeShape.was_marked t1 (Memory.mark memo1) (Memory.mark memo2))))))))))) ∧ (let mem0 : Memory.kind -> Memory.loc -> Memory.loc := Memory.accessor memo; (¬root = Memory.null ∧ TreeShape.is_tree (Memory.accessor memo) t root o1) ∧ (∀(memo1 : Memory.memory), TreeShape.unchanged (Memory.accessor memo) (Memory.accessor memo1) ∧ TreeShape.was_marked t (Memory.mark memo) (Memory.mark memo1) → TreeShape.rotated mem0 (Memory.accessor memo1) TreeShape.phase.Finish o1 ∧ (∀(x : Memory.loc), TreeShape.rotated mem0 (Memory.accessor memo1) TreeShape.phase.Finish x → TreeShape.rotated mem0 (Memory.accessor memo1) TreeShape.phase.Finish x ∧ (let o2 : Memory.loc := Memory.null; (TreeShape.ext (TreeShape.footprint t) mem0 (Memory.accessor memo1) ∧ TreeShape.is_tree mem0 t root o2) ∧ (TreeShape.is_tree (Memory.accessor memo1) t root o2 → TreeShape.is_tree (Memory.accessor memo1) t root Memory.null ∧ TreeShape.unchanged (Memory.accessor memo) (Memory.accessor memo1) ∧ TreeShape.was_marked t (Memory.mark memo) (Memory.mark memo1))))))
  := sorry
end verifythis_2016_tree_traversal_Recursive_markTreeqtvc
