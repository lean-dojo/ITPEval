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
namespace avl_AVL_balanceqtvc
axiom t : Type
axiom inhabited_axiom_t : Inhabited t
attribute [instance] inhabited_axiom_t
axiom zero : t
axiom op : t -> t -> t
axiom assoc (a : t) (b : t) (c : t) : op a (op b c) = op (op a b) c
axiom neutral (x : t) : op x zero = x ∧ x = op zero x
axiom agg :  {α : Type} -> [Inhabited α] -> (α -> t) -> List α -> t
axiom agg_empty {α : Type} [Inhabited α] (f : α -> t) : agg f ([] : List α) = zero
axiom agg_sing {α : Type} [Inhabited α] (s : List α) (f : α -> t) (fact0 : Int.ofNat (List.length s) = (1 : ℤ)) : agg f s = f (s[(0 : ℕ)]!)
axiom agg_cat {α : Type} [Inhabited α] (f : α -> t) (s1 : List α) (s2 : List α) : agg f (s1 ++ s2) = op (agg f s1) (agg f s2)
axiom t1 : Type -> Type
axiom inhabited_axiom_t1 {α : Type} [Inhabited α] : Inhabited (t1 α)
attribute [instance] inhabited_axiom_t1
axiom measure :  {α : Type} -> [Inhabited α] -> t1 α -> t
axiom balancing : ℕ
axiom balancing'def : (0 : ℤ) < Int.ofNat balancing
inductive tree (α : Type) where
  | Empty : tree α
  | Node : tree α -> t1 α -> tree α -> ℕ -> t -> tree α
axiom inhabited_axiom_tree {α : Type} [Inhabited α] : Inhabited (tree α)
attribute [instance] inhabited_axiom_tree
structure m (α : Type) where
  seq : List (t1 α)
  hgt : ℤ
axiom inhabited_axiom_m {α : Type} [Inhabited α] : Inhabited (m α)
attribute [instance] inhabited_axiom_m
noncomputable def node_model {α : Type} [Inhabited α] (l : List α) (d : α) (r : List α) := l ++ List.cons d r
noncomputable def seq_model {α : Type} [Inhabited α] : tree α -> List (t1 α)
  | (tree.Empty : tree α) => ([] : List (t1 α))
  | (tree.Node l d r x x0) => node_model (seq_model l) d (seq_model r)
noncomputable def real_height {α : Type} [Inhabited α] : tree α -> ℤ
  | (tree.Empty : tree α) => (0 : ℤ)
  | (tree.Node l x r x0 x1) => let hl : ℤ := real_height l; let hr : ℤ := real_height r; (1 : ℤ) + (if hl < hr then hr else hl)
axiom measure_closure :  {α : Type} -> [Inhabited α] -> t1 α -> t
axiom measure_closure_def {α : Type} [Inhabited α] (y : t1 α) : measure_closure y = measure y
noncomputable def balanced {α : Type} [Inhabited α] : tree α -> Prop
  | (tree.Empty : tree α) => True
  | (tree.Node l x r h m1) => Int.ofNat h = real_height (tree.Node l x r h m1) ∧ m1 = agg measure_closure (seq_model (tree.Node l x r h m1)) ∧ (-Int.ofNat balancing ≤ real_height r - real_height l ∧ real_height r - real_height l ≤ Int.ofNat balancing) ∧ balanced l ∧ balanced r
axiom t2 : Type -> Type
axiom inhabited_axiom_t2 {α : Type} [Inhabited α] : Inhabited (t2 α)
attribute [instance] inhabited_axiom_t2
axiom repr :  {α : Type} -> [Inhabited α] -> t2 α -> tree α
axiom m1 :  {α : Type} -> [Inhabited α] -> t2 α -> m α
axiom t'invariant {α : Type} [Inhabited α] (self : t2 α) : balanced (repr self) ∧ m.seq (m1 self) = seq_model (repr self) ∧ m.hgt (m1 self) = real_height (repr self)
noncomputable def t'eq {α : Type} [Inhabited α] (a : t2 α) (b : t2 α) := repr a = repr b ∧ m1 a = m1 b
axiom t'inj {α : Type} [Inhabited α] (a : t2 α) (b : t2 α) (fact0 : t'eq a b) : a = b
inductive view (α : Type) where
  | AEmpty : view α
  | ANode : t2 α -> t1 α -> t2 α -> ℕ -> t -> view α
axiom inhabited_axiom_view {α : Type} [Inhabited α] : Inhabited (view α)
attribute [instance] inhabited_axiom_view
theorem balance'vc {α : Type} [Inhabited α] (l : t2 α) (r : t2 α) (hl : ℕ) (hr : ℕ) (o1 : ℕ) (d : t1 α) (fact0 : -Int.ofNat balancing - (1 : ℤ) ≤ m.hgt (m1 l) - m.hgt (m1 r)) (fact1 : m.hgt (m1 l) - m.hgt (m1 r) ≤ Int.ofNat balancing + (1 : ℤ)) (fact2 : Int.ofNat hl = m.hgt (m1 l)) (fact3 : Int.ofNat hr = m.hgt (m1 r)) (fact4 : Int.ofNat o1 = -Int.ofNat hr) : Int.ofNat o1 ≤ Int.ofNat hl - Int.ofNat hr ∧ Int.ofNat hl - Int.ofNat hr ≤ Int.ofNat hl ∧ (∀(df : ℕ), Int.ofNat df = Int.ofNat hl - Int.ofNat hr → (if balancing < df then ∀(o2 : view α), (match o2 with | (view.AEmpty : view α) => m.hgt (m1 l) = (0 : ℤ) ∧ m.seq (m1 l) = ([] : List (t1 α)) | view.ANode l1 d r1 h s => m.seq (m1 l) = node_model (m.seq (m1 l1)) d (m.seq (m1 r1)) ∧ s = agg measure_closure (m.seq (m1 l)) ∧ (let hl1 : ℤ := m.hgt (m1 l1); let hr1 : ℤ := m.hgt (m1 r1); (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing) ∧ m.hgt (m1 l) = Int.ofNat h ∧ Int.ofNat h = (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1))) → (match o2 with | (view.AEmpty : view α) => False | view.ANode ll ld lr _ _ => (∀(o3 : ℕ), Int.ofNat o3 = m.hgt (m1 lr) → (∀(o4 : ℕ), Int.ofNat o4 = m.hgt (m1 ll) → (if o3 ≤ o4 then (-Int.ofNat balancing ≤ m.hgt (m1 lr) - m.hgt (m1 r) ∧ m.hgt (m1 lr) - m.hgt (m1 r) ≤ Int.ofNat balancing) ∧ (∀(o5 : t2 α), m.seq (m1 o5) = node_model (m.seq (m1 lr)) d (m.seq (m1 r)) ∧ m.hgt (m1 o5) = (1 : ℤ) + (if m.hgt (m1 lr) < m.hgt (m1 r) then m.hgt (m1 r) else m.hgt (m1 lr)) → -Int.ofNat balancing ≤ m.hgt (m1 ll) - m.hgt (m1 o5) ∧ m.hgt (m1 ll) - m.hgt (m1 o5) ≤ Int.ofNat balancing) else ∀(o5 : view α), (match o5 with | (view.AEmpty : view α) => m.hgt (m1 lr) = (0 : ℤ) ∧ m.seq (m1 lr) = ([] : List (t1 α)) | view.ANode l1 d1 r1 h s => m.seq (m1 lr) = node_model (m.seq (m1 l1)) d1 (m.seq (m1 r1)) ∧ s = agg measure_closure (m.seq (m1 lr)) ∧ (let hl1 : ℤ := m.hgt (m1 l1); let hr1 : ℤ := m.hgt (m1 r1); (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing) ∧ m.hgt (m1 lr) = Int.ofNat h ∧ Int.ofNat h = (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1))) → (match o5 with | (view.AEmpty : view α) => False | view.ANode lrl lrd lrr _ _ => (-Int.ofNat balancing ≤ m.hgt (m1 lrr) - m.hgt (m1 r) ∧ m.hgt (m1 lrr) - m.hgt (m1 r) ≤ Int.ofNat balancing) ∧ (∀(o6 : t2 α), m.seq (m1 o6) = node_model (m.seq (m1 lrr)) d (m.seq (m1 r)) ∧ m.hgt (m1 o6) = (1 : ℤ) + (if m.hgt (m1 lrr) < m.hgt (m1 r) then m.hgt (m1 r) else m.hgt (m1 lrr)) → (-Int.ofNat balancing ≤ m.hgt (m1 ll) - m.hgt (m1 lrl) ∧ m.hgt (m1 ll) - m.hgt (m1 lrl) ≤ Int.ofNat balancing) ∧ (∀(o7 : t2 α), m.seq (m1 o7) = node_model (m.seq (m1 ll)) ld (m.seq (m1 lrl)) ∧ m.hgt (m1 o7) = (1 : ℤ) + (if m.hgt (m1 ll) < m.hgt (m1 lrl) then m.hgt (m1 lrl) else m.hgt (m1 ll)) → -Int.ofNat balancing ≤ m.hgt (m1 o7) - m.hgt (m1 o6) ∧ m.hgt (m1 o7) - m.hgt (m1 o6) ≤ Int.ofNat balancing))))))) else ∀(o2 : ℕ), Int.ofNat o2 = -Int.ofNat balancing → (if df < o2 then ∀(o3 : view α), (match o3 with | (view.AEmpty : view α) => m.hgt (m1 r) = (0 : ℤ) ∧ m.seq (m1 r) = ([] : List (t1 α)) | view.ANode l1 d1 r1 h s => m.seq (m1 r) = node_model (m.seq (m1 l1)) d1 (m.seq (m1 r1)) ∧ s = agg measure_closure (m.seq (m1 r)) ∧ (let hl1 : ℤ := m.hgt (m1 l1); let hr1 : ℤ := m.hgt (m1 r1); (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing) ∧ m.hgt (m1 r) = Int.ofNat h ∧ Int.ofNat h = (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1))) → (match o3 with | (view.AEmpty : view α) => False | view.ANode rl rd rr _ _ => (∀(o4 : ℕ), Int.ofNat o4 = m.hgt (m1 rl) → (∀(o5 : ℕ), Int.ofNat o5 = m.hgt (m1 rr) → (if o4 ≤ o5 then (-Int.ofNat balancing ≤ m.hgt (m1 l) - m.hgt (m1 rl) ∧ m.hgt (m1 l) - m.hgt (m1 rl) ≤ Int.ofNat balancing) ∧ (∀(o6 : t2 α), m.seq (m1 o6) = node_model (m.seq (m1 l)) d (m.seq (m1 rl)) ∧ m.hgt (m1 o6) = (1 : ℤ) + (if m.hgt (m1 l) < m.hgt (m1 rl) then m.hgt (m1 rl) else m.hgt (m1 l)) → -Int.ofNat balancing ≤ m.hgt (m1 o6) - m.hgt (m1 rr) ∧ m.hgt (m1 o6) - m.hgt (m1 rr) ≤ Int.ofNat balancing) else ∀(o6 : view α), (match o6 with | (view.AEmpty : view α) => m.hgt (m1 rl) = (0 : ℤ) ∧ m.seq (m1 rl) = ([] : List (t1 α)) | view.ANode l1 d1 r1 h s => m.seq (m1 rl) = node_model (m.seq (m1 l1)) d1 (m.seq (m1 r1)) ∧ s = agg measure_closure (m.seq (m1 rl)) ∧ (let hl1 : ℤ := m.hgt (m1 l1); let hr1 : ℤ := m.hgt (m1 r1); (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing) ∧ m.hgt (m1 rl) = Int.ofNat h ∧ Int.ofNat h = (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1))) → (match o6 with | (view.AEmpty : view α) => False | view.ANode rll rld rlr _ _ => (-Int.ofNat balancing ≤ m.hgt (m1 rlr) - m.hgt (m1 rr) ∧ m.hgt (m1 rlr) - m.hgt (m1 rr) ≤ Int.ofNat balancing) ∧ (∀(o7 : t2 α), m.seq (m1 o7) = node_model (m.seq (m1 rlr)) rd (m.seq (m1 rr)) ∧ m.hgt (m1 o7) = (1 : ℤ) + (if m.hgt (m1 rlr) < m.hgt (m1 rr) then m.hgt (m1 rr) else m.hgt (m1 rlr)) → (-Int.ofNat balancing ≤ m.hgt (m1 l) - m.hgt (m1 rll) ∧ m.hgt (m1 l) - m.hgt (m1 rll) ≤ Int.ofNat balancing) ∧ (∀(o8 : t2 α), m.seq (m1 o8) = node_model (m.seq (m1 l)) d (m.seq (m1 rll)) ∧ m.hgt (m1 o8) = (1 : ℤ) + (if m.hgt (m1 l) < m.hgt (m1 rll) then m.hgt (m1 rll) else m.hgt (m1 l)) → -Int.ofNat balancing ≤ m.hgt (m1 o8) - m.hgt (m1 o7) ∧ m.hgt (m1 o8) - m.hgt (m1 o7) ≤ Int.ofNat balancing))))))) else -Int.ofNat balancing ≤ m.hgt (m1 l) - m.hgt (m1 r) ∧ m.hgt (m1 l) - m.hgt (m1 r) ≤ Int.ofNat balancing)) ∧ (∀(result : t2 α), (if balancing < df then ∃(o2 : view α), (match o2 with | (view.AEmpty : view α) => m.hgt (m1 l) = (0 : ℤ) ∧ m.seq (m1 l) = ([] : List (t1 α)) | view.ANode l1 d1 r1 h s => m.seq (m1 l) = node_model (m.seq (m1 l1)) d1 (m.seq (m1 r1)) ∧ s = agg measure_closure (m.seq (m1 l)) ∧ (let hl1 : ℤ := m.hgt (m1 l1); let hr1 : ℤ := m.hgt (m1 r1); (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing) ∧ m.hgt (m1 l) = Int.ofNat h ∧ Int.ofNat h = (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1))) ∧ (match o2 with | (view.AEmpty : view α) => False | view.ANode ll ld lr _ _ => (∃(o3 : ℕ), Int.ofNat o3 = m.hgt (m1 lr) ∧ (∃(o4 : ℕ), Int.ofNat o4 = m.hgt (m1 ll) ∧ (if o3 ≤ o4 then ∃(o5 : t2 α), (m.seq (m1 o5) = node_model (m.seq (m1 lr)) d (m.seq (m1 r)) ∧ m.hgt (m1 o5) = (1 : ℤ) + (if m.hgt (m1 lr) < m.hgt (m1 r) then m.hgt (m1 r) else m.hgt (m1 lr))) ∧ m.seq (m1 result) = node_model (m.seq (m1 ll)) ld (m.seq (m1 o5)) ∧ m.hgt (m1 result) = (1 : ℤ) + (if m.hgt (m1 ll) < m.hgt (m1 o5) then m.hgt (m1 o5) else m.hgt (m1 ll)) else ∃(o5 : view α), (match o5 with | (view.AEmpty : view α) => m.hgt (m1 lr) = (0 : ℤ) ∧ m.seq (m1 lr) = ([] : List (t1 α)) | view.ANode l1 d1 r1 h s => m.seq (m1 lr) = node_model (m.seq (m1 l1)) d1 (m.seq (m1 r1)) ∧ s = agg measure_closure (m.seq (m1 lr)) ∧ (let hl1 : ℤ := m.hgt (m1 l1); let hr1 : ℤ := m.hgt (m1 r1); (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing) ∧ m.hgt (m1 lr) = Int.ofNat h ∧ Int.ofNat h = (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1))) ∧ (match o5 with | (view.AEmpty : view α) => False | view.ANode lrl lrd lrr _ _ => (∃(o6 : t2 α), (m.seq (m1 o6) = node_model (m.seq (m1 lrr)) d (m.seq (m1 r)) ∧ m.hgt (m1 o6) = (1 : ℤ) + (if m.hgt (m1 lrr) < m.hgt (m1 r) then m.hgt (m1 r) else m.hgt (m1 lrr))) ∧ (∃(o7 : t2 α), (m.seq (m1 o7) = node_model (m.seq (m1 ll)) ld (m.seq (m1 lrl)) ∧ m.hgt (m1 o7) = (1 : ℤ) + (if m.hgt (m1 ll) < m.hgt (m1 lrl) then m.hgt (m1 lrl) else m.hgt (m1 ll))) ∧ m.seq (m1 result) = node_model (m.seq (m1 o7)) lrd (m.seq (m1 o6)) ∧ m.hgt (m1 result) = (1 : ℤ) + (if m.hgt (m1 o7) < m.hgt (m1 o6) then m.hgt (m1 o6) else m.hgt (m1 o7))))))))) else ∃(o2 : ℕ), Int.ofNat o2 = -Int.ofNat balancing ∧ (if df < o2 then ∃(o3 : view α), (match o3 with | (view.AEmpty : view α) => m.hgt (m1 r) = (0 : ℤ) ∧ m.seq (m1 r) = ([] : List (t1 α)) | view.ANode l1 d1 r1 h s => m.seq (m1 r) = node_model (m.seq (m1 l1)) d1 (m.seq (m1 r1)) ∧ s = agg measure_closure (m.seq (m1 r)) ∧ (let hl1 : ℤ := m.hgt (m1 l1); let hr1 : ℤ := m.hgt (m1 r1); (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing) ∧ m.hgt (m1 r) = Int.ofNat h ∧ Int.ofNat h = (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1))) ∧ (match o3 with | (view.AEmpty : view α) => False | view.ANode rl rd rr _ _ => (∃(o4 : ℕ), Int.ofNat o4 = m.hgt (m1 rl) ∧ (∃(o5 : ℕ), Int.ofNat o5 = m.hgt (m1 rr) ∧ (if o4 ≤ o5 then ∃(o6 : t2 α), (m.seq (m1 o6) = node_model (m.seq (m1 l)) d (m.seq (m1 rl)) ∧ m.hgt (m1 o6) = (1 : ℤ) + (if m.hgt (m1 l) < m.hgt (m1 rl) then m.hgt (m1 rl) else m.hgt (m1 l))) ∧ m.seq (m1 result) = node_model (m.seq (m1 o6)) rd (m.seq (m1 rr)) ∧ m.hgt (m1 result) = (1 : ℤ) + (if m.hgt (m1 o6) < m.hgt (m1 rr) then m.hgt (m1 rr) else m.hgt (m1 o6)) else ∃(o6 : view α), (match o6 with | (view.AEmpty : view α) => m.hgt (m1 rl) = (0 : ℤ) ∧ m.seq (m1 rl) = ([] : List (t1 α)) | view.ANode l1 d1 r1 h s => m.seq (m1 rl) = node_model (m.seq (m1 l1)) d1 (m.seq (m1 r1)) ∧ s = agg measure_closure (m.seq (m1 rl)) ∧ (let hl1 : ℤ := m.hgt (m1 l1); let hr1 : ℤ := m.hgt (m1 r1); (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing) ∧ m.hgt (m1 rl) = Int.ofNat h ∧ Int.ofNat h = (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1))) ∧ (match o6 with | (view.AEmpty : view α) => False | view.ANode rll rld rlr _ _ => (∃(o7 : t2 α), (m.seq (m1 o7) = node_model (m.seq (m1 rlr)) rd (m.seq (m1 rr)) ∧ m.hgt (m1 o7) = (1 : ℤ) + (if m.hgt (m1 rlr) < m.hgt (m1 rr) then m.hgt (m1 rr) else m.hgt (m1 rlr))) ∧ (∃(o8 : t2 α), (m.seq (m1 o8) = node_model (m.seq (m1 l)) d (m.seq (m1 rll)) ∧ m.hgt (m1 o8) = (1 : ℤ) + (if m.hgt (m1 l) < m.hgt (m1 rll) then m.hgt (m1 rll) else m.hgt (m1 l))) ∧ m.seq (m1 result) = node_model (m.seq (m1 o8)) rld (m.seq (m1 o7)) ∧ m.hgt (m1 result) = (1 : ℤ) + (if m.hgt (m1 o8) < m.hgt (m1 o7) then m.hgt (m1 o7) else m.hgt (m1 o8))))))))) else m.seq (m1 result) = node_model (m.seq (m1 l)) d (m.seq (m1 r)) ∧ m.hgt (m1 result) = (1 : ℤ) + (if m.hgt (m1 l) < m.hgt (m1 r) then m.hgt (m1 r) else m.hgt (m1 l)))) → m.seq (m1 result) = node_model (m.seq (m1 l)) d (m.seq (m1 r)) ∧ (let hl1 : ℤ := m.hgt (m1 l); let hr1 : ℤ := m.hgt (m1 r); let he : ℤ := (1 : ℤ) + (if hl1 < hr1 then hr1 else hl1); let hres : ℤ := m.hgt (m1 result); ((0 : ℤ) ≤ he - hres ∧ he - hres ≤ (1 : ℤ)) ∧ (-Int.ofNat balancing ≤ hl1 - hr1 ∧ hl1 - hr1 ≤ Int.ofNat balancing → he = hres))))
  := sorry
end avl_AVL_balanceqtvc
