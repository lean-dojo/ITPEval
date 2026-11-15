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
namespace IntInf
inductive t where
  | Finite : ℤ -> t
  | Infinite : t
axiom inhabited_axiom_t : Inhabited t
attribute [instance] inhabited_axiom_t
noncomputable def add (x : t) (y : t) := match x with | t.Infinite => t.Infinite | t.Finite x1 => (match y with | t.Infinite => t.Infinite | t.Finite y1 => t.Finite (x1 + y1))
noncomputable def eq (x : t) (y : t) := match (x, y) with | (t.Infinite, t.Infinite) => True | (t.Finite x1, t.Finite y1) => x1 = y1 | (_, _) => False
noncomputable def lt (x : t) (y : t) := match x with | t.Infinite => False | t.Finite x1 => (match y with | t.Infinite => True | t.Finite y1 => x1 < y1)
noncomputable def le (x : t) (y : t) := lt x y ∨ eq x y
axiom Refl (x : t) : le x x
axiom Trans (x : t) (y : t) (z : t) (fact0 : le x y) (fact1 : le y z) : le x z
axiom Antisymm (x : t) (y : t) (fact0 : le x y) (fact1 : le y x) : x = y
axiom Total (x : t) (y : t) : le x y ∨ le y x
end IntInf
namespace Const
axiom const :  {β : Type} -> [Inhabited β] ->  {α : Type} -> [Inhabited α] -> β -> α -> β
axiom const'def {β : Type} {α : Type} [Inhabited β] [Inhabited α] (v : β) (x : α) : (const : β -> α -> β) v x = v
end Const
namespace Graph
axiom vertex : Type
axiom inhabited_axiom_vertex : Inhabited vertex
attribute [instance] inhabited_axiom_vertex
axiom vertices : Finset vertex
axiom edges : Finset (vertex × vertex)
noncomputable def edge (x : vertex) (y : vertex) := (x, y) ∈ edges
axiom edges_def (x : vertex) (y : vertex) (fact0 : (x, y) ∈ edges) : x ∈ vertices ∧ y ∈ vertices
axiom s : vertex
axiom s'def : s ∈ vertices
inductive path : vertex -> List vertex -> vertex -> Prop where
 | Path_empty (x : vertex) : path x ([] : List vertex) x
 | Path_cons (x : vertex) (y : vertex) (l : List vertex) (z : vertex) : edge x y → path y l z → path x (List.cons x l) z
axiom path_right_extension (x : vertex) (l : List vertex) (y : vertex) (z : vertex) (fact0 : path x l y) (fact1 : edge y z) : path x (l ++ List.cons y ([] : List vertex)) z
axiom path_right_inversion (x : vertex) (l : List vertex) (z : vertex) (fact0 : path x l z) : x = z ∧ l = ([] : List vertex) ∨ (∃(y : vertex) (l' : List vertex), path x l' y ∧ edge y z ∧ l = l' ++ List.cons y ([] : List vertex))
axiom path_trans (x : vertex) (l1 : List vertex) (y : vertex) (l2 : List vertex) (z : vertex) (fact0 : path x l1 y) (fact1 : path y l2 z) : path x (l1 ++ l2) z
axiom empty_path (x : vertex) (y : vertex) (fact0 : path x ([] : List vertex) y) : x = y
axiom path_decomposition (x : vertex) (l1 : List vertex) (y : vertex) (l2 : List vertex) (z : vertex) (fact0 : path x (l1 ++ List.cons y l2) z) : path x l1 y ∧ path y (List.cons y l2) z
axiom weight : vertex -> vertex -> ℤ
noncomputable def path_weight : List vertex -> vertex -> ℤ
  | ([] : List vertex), dst => (0 : ℤ)
  | (List.cons x ([] : List vertex)), dst => weight x dst
  | (List.cons x (List.cons y x0)), dst => weight x y + path_weight (List.cons y x0) dst
axiom path_weight_right_extension (l : List vertex) (x : vertex) (y : vertex) : path_weight (l ++ List.cons x ([] : List vertex)) y = path_weight l x + weight x y
axiom path_weight_decomposition (l1 : List vertex) (y : vertex) (l2 : List vertex) (z : vertex) : path_weight (l1 ++ List.cons y l2) z = path_weight l1 y + path_weight (List.cons y l2) z
noncomputable def pigeon_set (s1 : Finset vertex) := ∀(l : List vertex), (∀(e : vertex), e ∈ l → e ∈ s1) → Finset.card s1 < List.length l → (∃(e : vertex) (l1 : List vertex) (l2 : List vertex) (l3 : List vertex), l = l1 ++ List.cons e (l2 ++ List.cons e l3))
axiom Induction (s1 : Finset vertex) (fact0 : ∀(s1 : Finset vertex), s1 = ∅ → pigeon_set s1) (fact1 : ∀(s1 : Finset vertex), pigeon_set s1 → (∀(t : vertex), pigeon_set (insert t s1))) : pigeon_set s1
axiom corner (l : List vertex) (s1 : Finset vertex) (fact0 : List.length l = Finset.card s1) (fact1 : ∀(e : vertex), e ∈ l → e ∈ s1) : (∃(e : vertex) (l1 : List vertex) (l2 : List vertex) (l3 : List vertex), l = l1 ++ List.cons e (l2 ++ List.cons e l3)) ∨ (∀(e : vertex), e ∈ s1 → e ∈ l)
axiom pigeon_0 : pigeon_set (∅ : Finset vertex)
axiom pigeon_1 (s1 : Finset vertex) (t : vertex) (fact0 : pigeon_set s1) : pigeon_set (insert t s1)
axiom pigeon_2 (s1 : Finset vertex) : pigeon_set s1
axiom pigeonhole (l : List vertex) (s1 : Finset vertex) (fact0 : ∀(e : vertex), e ∈ l → e ∈ s1) (fact1 : Finset.card s1 < List.length l) : ∃(e : vertex) (l1 : List vertex) (l2 : List vertex) (l3 : List vertex), l = l1 ++ List.cons e (l2 ++ List.cons e l3)
noncomputable def cyc_decomp (v : vertex) (l : List vertex) (vi : vertex) (l1 : List vertex) (l2 : List vertex) (l3 : List vertex) := l = (l1 ++ l2) ++ l3 ∧ (0 : ℤ) < Int.ofNat (List.length l2) ∧ path s l1 vi ∧ path vi l2 vi ∧ path vi l3 v
noncomputable def negative_cycle (v : vertex) := v ∈ vertices ∧ (∃(l1 : List vertex), path s l1 v) ∧ (∃(l2 : List vertex), path v l2 v ∧ path_weight l2 v < (0 : ℤ))
noncomputable def all_path_gt (v : vertex) (n : ℤ) := ∀(l : List vertex), path s l v ∧ List.length l < Finset.card vertices → n ≤ path_weight l v
end Graph
namespace bellman_ford_BellmanFord_bellman_fordqtvc
axiom set : Type
axiom inhabited_axiom_set : Inhabited set
attribute [instance] inhabited_axiom_set
axiom to_fset : set -> Finset (Graph.vertex × Graph.vertex)
axiom choose1 : set -> Graph.vertex × Graph.vertex
axiom choose'spec (s : set) (fact0 : ¬to_fset s = ∅) : choose1 s ∈ to_fset s
axiom t : Type -> Type
axiom inhabited_axiom_t {α : Type} [Inhabited α] : Inhabited (t α)
attribute [instance] inhabited_axiom_t
axiom contents :  {α : Type} -> [Inhabited α] -> t α -> Graph.vertex -> α
axiom create :  {α : Type} -> [Inhabited α] -> α -> t α
axiom create'spec {α : Type} [Inhabited α] (x : α) : contents (create x) = Const.const x
axiom mixfix_lbrb :  {α : Type} -> [Inhabited α] -> t α -> Graph.vertex -> α
axiom mixfix_lbrb'spec {α : Type} [Inhabited α] (m : t α) (k : Graph.vertex) : mixfix_lbrb m k = contents m k
axiom mixfix_lblsmnrb :  {α : Type} -> [Inhabited α] -> t α -> Graph.vertex -> α -> t α
axiom mixfix_lblsmnrb'spec {α : Type} [Inhabited α] (m : t α) (k : Graph.vertex) (v : α) : contents (mixfix_lblsmnrb m k v) = Function.update (contents m) k v
axiom distmap : Type
axiom inhabited_axiom_distmap : Inhabited distmap
attribute [instance] inhabited_axiom_distmap
noncomputable def inv1 (m : t IntInf.t) (pass : ℤ) (via : Finset (Graph.vertex × Graph.vertex)) := ∀(v : Graph.vertex), v ∈ Graph.vertices → (match mixfix_lbrb m v with | IntInf.t.Finite n => (∃(l : List Graph.vertex), Graph.path Graph.s l v ∧ Graph.path_weight l v = n) ∧ (∀(l : List Graph.vertex), Graph.path Graph.s l v → Int.ofNat (List.length l) < pass → n ≤ Graph.path_weight l v) ∧ (∀(u : Graph.vertex) (l : List Graph.vertex), Graph.path Graph.s l u → Int.ofNat (List.length l) < pass → (u, v) ∈ via → n ≤ Graph.path_weight l u + Graph.weight u v) | IntInf.t.Infinite => (∀(l : List Graph.vertex), Graph.path Graph.s l v → pass ≤ Int.ofNat (List.length l)) ∧ (∀(u : Graph.vertex), (u, v) ∈ via → (∀(lu : List Graph.vertex), Graph.path Graph.s lu u → pass ≤ Int.ofNat (List.length lu))))
noncomputable def inv2 (m : t IntInf.t) (via : Finset (Graph.vertex × Graph.vertex)) := ∀(u : Graph.vertex) (v : Graph.vertex), (u, v) ∈ via → IntInf.le (mixfix_lbrb m v) (IntInf.add (mixfix_lbrb m u) (IntInf.t.Finite (Graph.weight u v)))
theorem bellman_ford'vc : let m : t IntInf.t := mixfix_lblsmnrb (create IntInf.t.Infinite) Graph.s (IntInf.t.Finite (0 : ℤ)); let o1 : ℤ := Int.ofNat (Finset.card Graph.vertices) - (1 : ℤ); ((1 : ℤ) ≤ o1 + (1 : ℤ) → inv1 m (1 : ℤ) (∅ : Finset (Graph.vertex × Graph.vertex)) ∧ (∀(m1 : t IntInf.t), (∀(i : ℤ), ((1 : ℤ) ≤ i ∧ i ≤ o1) ∧ inv1 m1 i (∅ : Finset (Graph.vertex × Graph.vertex)) → (∀(es : set), to_fset es = Graph.edges → (to_fset es ⊆ Graph.edges ∧ inv1 m1 i (Graph.edges \ to_fset es)) ∧ (∀(es1 : set) (m2 : t IntInf.t), to_fset es1 ⊆ Graph.edges ∧ inv1 m2 i (Graph.edges \ to_fset es1) → (if ¬to_fset es1 = ∅ then let via : Finset (Graph.vertex × Graph.vertex) := Graph.edges \ to_fset es1; ¬to_fset es1 = ∅ ∧ (∀(es2 : set), let o2 : Graph.vertex × Graph.vertex := choose1 es1; o2 ∈ to_fset es1 ∧ to_fset es2 = Finset.erase (to_fset es1) o2 → (match o2 with | (u, v) => (((1 : ℤ) ≤ i ∧ (u, v) ∈ Graph.edges ∧ ¬(u, v) ∈ via) ∧ inv1 m2 i via) ∧ (∀(m3 : t IntInf.t), inv1 m3 i (insert (u, v) via) → ((0 : ℤ) ≤ Int.ofNat (Finset.card (to_fset es1)) ∧ Finset.card (to_fset es2) < Finset.card (to_fset es1)) ∧ to_fset es2 ⊆ Graph.edges ∧ inv1 m3 i (Graph.edges \ to_fset es2)))) else inv1 m2 (i + (1 : ℤ)) (∅ : Finset (Graph.vertex × Graph.vertex)))))) ∧ (inv1 m1 (o1 + (1 : ℤ)) (∅ : Finset (Graph.vertex × Graph.vertex)) → (∀(es : set), to_fset es = Graph.edges → (to_fset es ⊆ Graph.edges ∧ inv2 m1 (Graph.edges \ to_fset es)) ∧ (∀(es1 : set), to_fset es1 ⊆ Graph.edges ∧ inv2 m1 (Graph.edges \ to_fset es1) → (if ¬to_fset es1 = ∅ then ¬to_fset es1 = ∅ ∧ (∀(es2 : set), let o2 : Graph.vertex × Graph.vertex := choose1 es1; o2 ∈ to_fset es1 ∧ to_fset es2 = Finset.erase (to_fset es1) o2 → (match o2 with | (u, v) => (let o3 : IntInf.t := mixfix_lbrb m1 v; o3 = contents m1 v → (let o4 : IntInf.t := mixfix_lbrb m1 u; o4 = contents m1 u → (if IntInf.lt (IntInf.add o4 (IntInf.t.Finite (Graph.weight u v))) o3 then ∃(v1 : Graph.vertex), Graph.negative_cycle v1 else ((0 : ℤ) ≤ Int.ofNat (Finset.card (to_fset es1)) ∧ Finset.card (to_fset es2) < Finset.card (to_fset es1)) ∧ to_fset es2 ⊆ Graph.edges ∧ inv2 m1 (Graph.edges \ to_fset es2)))))) else ∀(v : Graph.vertex), v ∈ Graph.vertices → (match mixfix_lbrb m1 v with | IntInf.t.Finite n => (∃(l : List Graph.vertex), Graph.path Graph.s l v ∧ Graph.path_weight l v = n) ∧ (∀(l : List Graph.vertex), Graph.path Graph.s l v → n ≤ Graph.path_weight l v) | IntInf.t.Infinite => (∀(l : List Graph.vertex), ¬Graph.path Graph.s l v)))))))) ∧ (o1 + (1 : ℤ) < (1 : ℤ) → (∀(es : set), to_fset es = Graph.edges → (to_fset es ⊆ Graph.edges ∧ inv2 m (Graph.edges \ to_fset es)) ∧ (∀(es1 : set), to_fset es1 ⊆ Graph.edges ∧ inv2 m (Graph.edges \ to_fset es1) → (if ¬to_fset es1 = ∅ then ¬to_fset es1 = ∅ ∧ (∀(es2 : set), let o2 : Graph.vertex × Graph.vertex := choose1 es1; o2 ∈ to_fset es1 ∧ to_fset es2 = Finset.erase (to_fset es1) o2 → (match o2 with | (u, v) => (let o3 : IntInf.t := mixfix_lbrb m v; o3 = contents m v → (let o4 : IntInf.t := mixfix_lbrb m u; o4 = contents m u → (if IntInf.lt (IntInf.add o4 (IntInf.t.Finite (Graph.weight u v))) o3 then ∃(v1 : Graph.vertex), Graph.negative_cycle v1 else ((0 : ℤ) ≤ Int.ofNat (Finset.card (to_fset es1)) ∧ Finset.card (to_fset es2) < Finset.card (to_fset es1)) ∧ to_fset es2 ⊆ Graph.edges ∧ inv2 m (Graph.edges \ to_fset es2)))))) else ∀(v : Graph.vertex), v ∈ Graph.vertices → (match mixfix_lbrb m v with | IntInf.t.Finite n => (∃(l : List Graph.vertex), Graph.path Graph.s l v ∧ Graph.path_weight l v = n) ∧ (∀(l : List Graph.vertex), Graph.path Graph.s l v → n ≤ Graph.path_weight l v) | IntInf.t.Infinite => (∀(l : List Graph.vertex), ¬Graph.path Graph.s l v))))))
  := sorry
end bellman_ford_BellmanFord_bellman_fordqtvc
