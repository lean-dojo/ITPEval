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
namespace Memory
axiom loc : Type
axiom inhabited_axiom_loc : Inhabited loc
attribute [instance] inhabited_axiom_loc
axiom null : loc
axiom eq_loc : loc -> loc -> Prop
axiom eq_loc'spec (x : loc) (y : loc) : eq_loc x y = (x = y)
structure node where
  left1 : loc
  right1 : loc
  data : ℤ
axiom inhabited_axiom_node : Inhabited node
attribute [instance] inhabited_axiom_node
axiom memory : Type
axiom inhabited_axiom_memory : Inhabited memory
attribute [instance] inhabited_axiom_memory
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
namespace Inorder
noncomputable def inorder {α : Type} [Inhabited α] : Tree.tree α -> List α
  | (Tree.tree.Empty : Tree.tree α) => ([] : List α)
  | (Tree.tree.Node l x r) => inorder l ++ List.cons x (inorder r)
end Inorder
namespace verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc
noncomputable def root (t : Tree.tree Memory.loc) := match t with | (Tree.tree.Empty : Tree.tree Memory.loc) => Memory.null | Tree.tree.Node _ p _ => p
noncomputable def istree : (Memory.loc -> Memory.node) -> Tree.tree Memory.loc -> Prop
  | m, (Tree.tree.Empty : Tree.tree Memory.loc) => True
  | m, (Tree.tree.Node l p r) => ¬p = Memory.null ∧ istree m l ∧ istree m r ∧ root l = Memory.node.left1 (m p) ∧ root r = Memory.node.right1 (m p)
inductive zipper (α : Type) where
  | Top : zipper α
  | Left : zipper α -> α -> Tree.tree α -> zipper α
axiom inhabited_axiom_zipper {α : Type} [Inhabited α] : Inhabited (zipper α)
attribute [instance] inhabited_axiom_zipper
noncomputable def zip {α : Type} [Inhabited α] : Tree.tree α -> zipper α -> Tree.tree α
  | t, (zipper.Top : zipper α) => t
  | t, (zipper.Left z1 x r) => zip (Tree.tree.Node t x r) z1
noncomputable def inorderz {α : Type} [Inhabited α] : zipper α -> List α
  | (zipper.Top : zipper α) => ([] : List α)
  | (zipper.Left z1 x r) => List.cons x (Inorder.inorder r) ++ inorderz z1
theorem search_tree_delete_min'vc (it : Tree.tree Memory.loc) (mem : Memory.loc -> Memory.node) (fact0 : ¬root it = Memory.null) (fact1 : istree mem it) (fact2 : List.Nodup (Inorder.inorder it)) : ¬root it = Memory.null ∧ (let o1 : Memory.loc := Memory.node.left1 (mem (root it)); let o2 : Memory.loc := Memory.null; Memory.eq_loc o1 o2 = (o1 = o2) → (if Memory.eq_loc o1 o2 then ¬root it = Memory.null ∧ ¬root it = Memory.null ∧ (match it with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node l _ r => istree mem r ∧ root r = Memory.node.right1 (mem (root it)) ∧ (match Inorder.inorder it with | ([] : List Memory.loc) => False | List.cons p l1 => Memory.node.data (mem (root it)) = Memory.node.data (mem p) ∧ Inorder.inorder r = l1)) else ¬o1 = Memory.null ∧ ¬it = (Tree.tree.Empty : Tree.tree Memory.loc) ∧ (∀(o3 : Tree.tree Memory.loc), (match it with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node _ _ r => o3 = r) → ¬it = (Tree.tree.Empty : Tree.tree Memory.loc) ∧ (∀(o4 : Tree.tree Memory.loc), (match it with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node l _ _ => o4 = l) → ((¬root it = Memory.null ∧ Memory.node.left1 (mem (root it)) = o1) ∧ ¬o1 = Memory.null ∧ (let pt : Tree.tree Memory.loc := Tree.tree.Node o4 (root it) o3; istree mem pt ∧ zip pt zipper.Top = it)) ∧ (∀(subtree : Tree.tree Memory.loc) (ppr : Tree.tree Memory.loc) (zipper1 : zipper Memory.loc) (pp : Memory.loc), ¬pp = Memory.null ∧ ¬Memory.node.left1 (mem pp) = Memory.null ∧ (let pt : Tree.tree Memory.loc := Tree.tree.Node subtree pp ppr; istree mem pt ∧ zip pt zipper1 = it) → (let o5 : Memory.loc := Memory.null; Memory.eq_loc (Memory.node.left1 (mem (Memory.node.left1 (mem pp)))) o5 = (Memory.node.left1 (mem (Memory.node.left1 (mem pp))) = o5) → (if ¬Memory.eq_loc (Memory.node.left1 (mem (Memory.node.left1 (mem pp)))) o5 then ¬subtree = (Tree.tree.Empty : Tree.tree Memory.loc) ∧ (∀(o6 : Tree.tree Memory.loc), (match subtree with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node _ _ r => o6 = r) → ¬subtree = (Tree.tree.Empty : Tree.tree Memory.loc) ∧ (∀(o7 : Tree.tree Memory.loc), (match subtree with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node l _ _ => o7 = l) → ¬Memory.node.left1 (mem (Memory.node.left1 (mem pp))) = Memory.null ∧ (match subtree with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node f _ f1 => f = o7 ∨ f1 = o7) ∧ ¬Memory.node.left1 (mem pp) = Memory.null ∧ ¬Memory.node.left1 (mem (Memory.node.left1 (mem pp))) = Memory.null ∧ (let pt : Tree.tree Memory.loc := Tree.tree.Node o7 (Memory.node.left1 (mem pp)) o6; istree mem pt ∧ zip pt (zipper.Left zipper1 pp ppr) = it))) else ¬Memory.node.left1 (mem pp) = Memory.null ∧ ¬Memory.node.left1 (mem pp) = Memory.null ∧ ¬pp = Memory.null ∧ (∀(mem1 : Memory.loc -> Memory.node), mem1 pp = (let x_q' : Memory.node := mem pp; Memory.node.mk (Memory.node.right1 (mem (Memory.node.left1 (mem pp)))) (Memory.node.right1 x_q') (Memory.node.data x_q')) ∧ (∀(q : Memory.loc), ¬q = pp → mem1 q = mem q) → ¬subtree = (Tree.tree.Empty : Tree.tree Memory.loc) ∧ (∀(pl : Tree.tree Memory.loc), (match subtree with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node l _ _ => pl = l) → ¬subtree = (Tree.tree.Empty : Tree.tree Memory.loc) ∧ (∀(o6 : Tree.tree Memory.loc), (match subtree with | (Tree.tree.Empty : Tree.tree Memory.loc) => False | Tree.tree.Node _ _ r => o6 = r) → (∀(p : Memory.loc), Memory.node.data (mem1 p) = Memory.node.data (mem p)) ∧ istree mem1 (zip o6 (zipper.Left zipper1 pp ppr)) ∧ root (zip o6 (zipper.Left zipper1 pp ppr)) = root it ∧ (match Inorder.inorder it with | ([] : List Memory.loc) => False | List.cons p l => Memory.node.data (mem (Memory.node.left1 (mem pp))) = Memory.node.data (mem1 p) ∧ Inorder.inorder (zip o6 (zipper.Left zipper1 pp ppr)) = l)))))))))))
  := sorry
end verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc
