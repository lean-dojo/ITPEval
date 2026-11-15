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
namespace dijkstra_DijkstraShortestPath_shortest_path_codeqtvc
axiom vertex : Type
axiom inhabited_axiom_vertex : Inhabited vertex
attribute [instance] inhabited_axiom_vertex
axiom set : Type
axiom inhabited_axiom_set : Inhabited set
attribute [instance] inhabited_axiom_set
axiom to_fset : set -> Finset vertex
axiom choose1 : set -> vertex
axiom choose'spec (s : set) (fact0 : ¬to_fset s = ∅) : choose1 s ∈ to_fset s
axiom t : Type -> Type
axiom inhabited_axiom_t {α : Type} [Inhabited α] : Inhabited (t α)
attribute [instance] inhabited_axiom_t
axiom contents :  {α : Type} -> [Inhabited α] -> t α -> vertex -> α
axiom create :  {α : Type} -> [Inhabited α] -> α -> t α
axiom create'spec {α : Type} [Inhabited α] (x : α) : contents (create x) = Const.const x
axiom mixfix_lbrb :  {α : Type} -> [Inhabited α] -> t α -> vertex -> α
axiom mixfix_lbrb'spec {α : Type} [Inhabited α] (m : t α) (k : vertex) : mixfix_lbrb m k = contents m k
axiom mixfix_lblsmnrb :  {α : Type} -> [Inhabited α] -> t α -> vertex -> α -> t α
axiom mixfix_lblsmnrb'spec {α : Type} [Inhabited α] (m : t α) (k : vertex) (v : α) : contents (mixfix_lblsmnrb m k v) = Function.update (contents m) k v
axiom v : Finset vertex
axiom g_succ : vertex -> Finset vertex
axiom g_succ'spec (x_x : vertex) : g_succ x_x ⊆ v
axiom weight : vertex -> vertex -> ℤ
axiom weight'spec (x : vertex) (x_1 : vertex) : (0 : ℤ) ≤ weight x x_1
noncomputable def min (m : vertex) (q : set) (d : t ℤ) := m ∈ to_fset q ∧ (∀(x : vertex), x ∈ to_fset q → mixfix_lbrb d m ≤ mixfix_lbrb d x)
inductive path : vertex -> vertex -> ℤ -> Prop where
 | Path_nil (x : vertex) : path x x (0 : ℤ)
 | Path_cons (x : vertex) (y : vertex) (d : ℤ) (z : vertex) : path x y d → z ∈ g_succ y → path x z (d + weight y z)
noncomputable def shortest_path (x : vertex) (y : vertex) (d : ℤ) := path x y d ∧ (∀(d' : ℤ), path x y d' → d ≤ d')
noncomputable def inv_src (src : vertex) (s : set) (q : set) := src ∈ to_fset s ∨ src ∈ to_fset q
noncomputable def inv (src : vertex) (s : set) (q : set) (d : t ℤ) := inv_src src s q ∧ mixfix_lbrb d src = (0 : ℤ) ∧ to_fset s ⊆ v ∧ to_fset q ⊆ v ∧ (∀(v1 : vertex), v1 ∈ to_fset q → ¬v1 ∈ to_fset s) ∧ (∀(v1 : vertex), v1 ∈ to_fset s → shortest_path src v1 (mixfix_lbrb d v1)) ∧ (∀(v1 : vertex), v1 ∈ to_fset q → path src v1 (mixfix_lbrb d v1))
noncomputable def inv_succ (x_src : vertex) (s : set) (q : set) (d : t ℤ) := ∀(x : vertex), x ∈ to_fset s → (∀(y : vertex), y ∈ g_succ x → (y ∈ to_fset s ∨ y ∈ to_fset q) ∧ mixfix_lbrb d y ≤ mixfix_lbrb d x + weight x y)
noncomputable def inv_succ2 (x_src : vertex) (s : set) (q : set) (d : t ℤ) (u : vertex) (su : set) := ∀(x : vertex), x ∈ to_fset s → (∀(y : vertex), y ∈ g_succ x → ¬x = u ∨ x = u ∧ ¬y ∈ to_fset su → (y ∈ to_fset s ∨ y ∈ to_fset q) ∧ mixfix_lbrb d y ≤ mixfix_lbrb d x + weight x y)
theorem shortest_path_code'vc (src : vertex) (dst : vertex) (visited : set) (q : set) (d : t ℤ) (fact0 : src ∈ v) (fact1 : dst ∈ v) (fact2 : to_fset visited = ∅) (fact3 : to_fset q = insert src (∅ : Finset vertex)) : inv src visited q (mixfix_lblsmnrb d src (0 : ℤ)) ∧ inv_succ src visited q (mixfix_lblsmnrb d src (0 : ℤ)) ∧ (∀(m : vertex), min m q (mixfix_lblsmnrb d src (0 : ℤ)) → (∀(x : vertex) (dx : ℤ), path src x dx → dx < mixfix_lbrb (mixfix_lblsmnrb d src (0 : ℤ)) m → x ∈ to_fset visited)) ∧ (∀(q1 : set) (d1 : t ℤ) (visited1 : set), inv src visited1 q1 d1 ∧ inv_succ src visited1 q1 d1 ∧ (∀(m : vertex), min m q1 d1 → (∀(x : vertex) (dx : ℤ), path src x dx → dx < mixfix_lbrb d1 m → x ∈ to_fset visited1)) → (if ¬to_fset q1 = ∅ then ¬to_fset q1 = ∅ ∧ (∀(q2 : set) (u : vertex), min u q1 d1 ∧ to_fset q2 = Finset.erase (to_fset q1) u → (∀(visited2 : set), to_fset visited2 = insert u (to_fset visited1) ∧ (if u ∈ to_fset visited1 then Finset.card (to_fset visited2) = Finset.card (to_fset visited1) else Int.ofNat (Finset.card (to_fset visited2)) = Int.ofNat (Finset.card (to_fset visited1)) + (1 : ℤ)) → (∀(su : set), to_fset su = g_succ u → (to_fset su ⊆ g_succ u ∧ inv src visited2 q2 d1 ∧ inv_succ2 src visited2 q2 d1 u su) ∧ (∀(su1 : set) (q3 : set) (d2 : t ℤ), to_fset su1 ⊆ g_succ u ∧ inv src visited2 q3 d2 ∧ inv_succ2 src visited2 q3 d2 u su1 → (if ¬to_fset su1 = ∅ then ¬to_fset su1 = ∅ ∧ (∀(su2 : set), let v1 : vertex := choose1 su1; v1 ∈ to_fset su1 ∧ to_fset su2 = Finset.erase (to_fset su1) v1 → (∀(q4 : set) (d3 : t ℤ), v1 ∈ to_fset visited2 ∧ q4 = q3 ∧ d3 = d2 ∨ v1 ∈ to_fset q4 ∧ mixfix_lbrb d3 v1 ≤ mixfix_lbrb d3 u + weight u v1 ∧ q4 = q3 ∧ d3 = d2 ∨ v1 ∈ to_fset q4 ∧ mixfix_lbrb d2 u + weight u v1 < mixfix_lbrb d2 v1 ∧ q4 = q3 ∧ d3 = mixfix_lblsmnrb d2 v1 (mixfix_lbrb d2 u + weight u v1) ∨ ¬v1 ∈ to_fset visited2 ∧ ¬v1 ∈ to_fset q3 ∧ to_fset q4 = insert v1 (to_fset q3) ∧ d3 = mixfix_lblsmnrb d2 v1 (mixfix_lbrb d2 u + weight u v1) → ((0 : ℤ) ≤ Int.ofNat (Finset.card (to_fset su1)) ∧ Finset.card (to_fset su2) < Finset.card (to_fset su1)) ∧ to_fset su2 ⊆ g_succ u ∧ inv src visited2 q4 d3 ∧ inv_succ2 src visited2 q4 d3 u su2)) else ((0 : ℤ) ≤ Int.ofNat (Finset.card v) - Int.ofNat (Finset.card (to_fset visited1)) ∧ Int.ofNat (Finset.card v) - Int.ofNat (Finset.card (to_fset visited2)) < Int.ofNat (Finset.card v) - Int.ofNat (Finset.card (to_fset visited1))) ∧ inv src visited2 q3 d2 ∧ inv_succ src visited2 q3 d2 ∧ (∀(m : vertex), min m q3 d2 → (∀(x : vertex) (dx : ℤ), path src x dx → dx < mixfix_lbrb d2 m → x ∈ to_fset visited2))))))) else (∀(v1 : vertex), v1 ∈ to_fset visited1 → shortest_path src v1 (mixfix_lbrb d1 v1)) ∧ (∀(v1 : vertex), ¬v1 ∈ to_fset visited1 → (∀(dv : ℤ), ¬path src v1 dv))))
  := sorry
end dijkstra_DijkstraShortestPath_shortest_path_codeqtvc
