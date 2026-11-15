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

namespace ArithmeticResults
end ArithmeticResults
namespace DivisibilityResults
end DivisibilityResults
namespace EulerSieveSpec
noncomputable def inv_nexts (nexts : List ℤ) (n : ℤ) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → i < nexts[Int.toNat i]! ∧ nexts[Int.toNat i]! ≤ n
noncomputable def all_eliminated_marked (marked : List Bool) (nexts : List ℤ) := List.length marked = List.length nexts ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length marked) → (∀(j : ℤ), i < j ∧ j < nexts[Int.toNat i]! → marked[Int.toNat j]! = true))
noncomputable def all_eliminated_marked_partial (marked : List Bool) (nexts : List ℤ) (min : ℤ) := List.length marked = List.length nexts ∧ (∀(i : ℤ), min ≤ i ∧ i < Int.ofNat (List.length marked) → (∀(j : ℤ), i < j ∧ j < nexts[Int.toNat i]! → marked[Int.toNat j]! = true))
noncomputable def not_marked_impl_next_not_marked (marked_old : List Bool) (nexts : List ℤ) (n : ℤ) := List.length marked_old = List.length nexts ∧ (2 : ℤ) ≤ Int.ofNat (List.length marked_old) ∧ (2 : ℤ) ≤ n ∧ (∀(i : ℤ), (2 : ℤ) ≤ i ∧ i ≤ (Int.ofNat (List.length marked_old) - (1 : ℤ)) / n → nexts[Int.toNat i]! ≤ (Int.ofNat (List.length marked_old) - (1 : ℤ)) / n → ¬marked_old[Int.toNat i]! = true → ¬marked_old[Int.toNat (nexts[Int.toNat i]!)]! = true)
noncomputable def is_copy (marked : List Bool) (marked_old : List Bool) := List.length marked = List.length marked_old ∧ (∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < Int.ofNat (List.length marked) → ¬marked[Int.toNat i]! = true → ¬marked_old[Int.toNat i]! = true)
noncomputable def not_marked_impl_next_not_marked_partial (marked : List Bool) (nexts : List ℤ) (n : ℤ) (p : ℤ) := List.length marked = List.length nexts ∧ (2 : ℤ) ≤ Int.ofNat (List.length marked) ∧ (2 : ℤ) ≤ n ∧ p ≤ (Int.ofNat (List.length marked) - (1 : ℤ)) / n ∧ (∀(i : ℤ), (2 : ℤ) ≤ i ∧ i < p → nexts[Int.toNat i]! ≤ (Int.ofNat (List.length marked) - (1 : ℤ)) / n → ¬marked[Int.toNat i]! = true → ¬marked[Int.toNat (nexts[Int.toNat i]!)]! = true)
noncomputable def all_primes (marked : List Bool) (n : ℤ) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → (¬marked[Int.toNat i]! = true) = Nat.Prime (Int.toNat i)
noncomputable def all_multiples_marked (marked : List Bool) (i : ℤ) (max : ℤ) := ((2 : ℤ) ≤ i ∧ i < Int.ofNat (List.length marked)) ∧ (∀(k : ℤ), (2 : ℤ) ≤ k ∧ k < max → i * k < Int.ofNat (List.length marked) → marked[Int.toNat (i * k)]! = true)
noncomputable def previously_marked_multiples (marked : List Bool) (n : ℤ) := ∀(i : ℤ), (2 : ℤ) ≤ i ∧ i < n → all_multiples_marked marked i (Int.ofNat (List.length marked))
noncomputable def only_multiples_marked (marked : List Bool) (n : ℤ) := ∀(k : ℤ), (2 : ℤ) ≤ k ∧ k < Int.ofNat (List.length marked) → marked[Int.toNat k]! = true → (∃(i : ℤ) (j : ℤ), ((2 : ℤ) ≤ i ∧ i < n) ∧ ((2 : ℤ) ≤ j ∧ j < Int.ofNat (List.length marked)) ∧ i * j = k)
noncomputable def prime_multiples_marked (marked_old : List Bool) (marked : List Bool) (n : ℤ) (max : ℤ) := List.length marked_old = List.length marked ∧ (n < max ∧ max ≤ Int.ofNat (List.length marked)) ∧ (∀(i : ℤ), n ≤ i ∧ i < max → ¬marked_old[Int.toNat i]! = true → n * i < Int.ofNat (List.length marked_old) → marked[Int.toNat (n * i)]! = true)
noncomputable def inv_remove_products (nexts : List ℤ) (marked : List Bool) (n : ℤ) := List.length nexts = List.length marked ∧ ¬marked[(2 : ℕ)]! = true ∧ all_primes marked n ∧ Nat.Prime (Int.toNat n) ∧ ¬marked[Int.toNat n]! = true ∧ inv_nexts nexts (Int.ofNat (List.length nexts))
noncomputable def ordered (a : List ℤ) (n : ℤ) := ∀(i : ℤ) (j : ℤ), (0 : ℤ) ≤ i ∧ i < j ∧ j < n → a[Int.toNat i]! < a[Int.toNat j]!
noncomputable def all_inf_or_eq (a : List ℤ) (n : ℤ) (k : ℤ) := ∀(i : ℤ), (0 : ℤ) ≤ i ∧ i < n → a[Int.toNat i]! ≤ k
end EulerSieveSpec
namespace euler_sieve_EulerSieve_remove_productsqtvc
axiom t : Type
axiom inhabited_axiom_t : Inhabited t
attribute [instance] inhabited_axiom_t
axiom nexts : t -> List ℤ
axiom marked : t -> List Bool
axiom max : t -> BitVec 63
axiom t'invariant (self : t) : BitVec.toInt (max self) < BitVec.toInt int'63_max ∧ (3 : ℤ) ≤ BitVec.toInt (max self) ∧ List.length (nexts self) = List.length (marked self) ∧ Int.ofNat (List.length (marked self)) = BitVec.toInt (max self) + (1 : ℤ) ∧ EulerSieveSpec.inv_nexts (nexts self) (Int.ofNat (List.length (nexts self))) ∧ EulerSieveSpec.all_eliminated_marked (marked self) (nexts self) ∧ (∀(i : ℤ), (3 : ℤ) ≤ i ∧ i ≤ BitVec.toInt (max self) → i % (2 : ℤ) = (0 : ℤ) → (marked self)[Int.toNat i]! = true) ∧ (∀(i : ℤ), (3 : ℤ) ≤ i ∧ i < BitVec.toInt (max self) - (1 : ℤ) → i % (2 : ℤ) = (1 : ℤ) → (nexts self)[Int.toNat i]! % (2 : ℤ) = (1 : ℤ) ∨ (nexts self)[Int.toNat i]! = BitVec.toInt (max self) + (1 : ℤ)) ∧ (nexts self)[Int.toNat (BitVec.toInt (max self))]! = BitVec.toInt (max self) + (1 : ℤ) ∧ ((BitVec.toInt (max self) - (1 : ℤ)) % (2 : ℤ) = (0 : ℤ) → (nexts self)[Int.toNat (BitVec.toInt (max self) - (1 : ℤ))]! = BitVec.toInt (max self)) ∧ ((BitVec.toInt (max self) - (1 : ℤ)) % (2 : ℤ) = (1 : ℤ) → (nexts self)[Int.toNat (BitVec.toInt (max self) - (1 : ℤ))]! = BitVec.toInt (max self) + (1 : ℤ))
theorem remove_products'vc (n : BitVec 63) (t1 : t) (fact0 : (3 : ℤ) ≤ BitVec.toInt n) (fact1 : BitVec.toInt n ≤ BitVec.toInt (max t1)) (fact2 : BitVec.toInt n * BitVec.toInt n ≤ BitVec.toInt (max t1)) (fact3 : EulerSieveSpec.inv_remove_products (nexts t1) (marked t1) (BitVec.toInt n)) (fact4 : EulerSieveSpec.previously_marked_multiples (marked t1) (BitVec.toInt n)) (fact5 : EulerSieveSpec.only_multiples_marked (marked t1) (BitVec.toInt n)) (fact6 : EulerSieveSpec.not_marked_impl_next_not_marked (marked t1) (nexts t1) (BitVec.toInt n)) : let o1 : BitVec 63 := max t1; (2 : ℤ) ≤ BitVec.toInt o1 → (¬BitVec.toInt n = (0 : ℤ) ∧ int'63_in_bounds (Int.tdiv (BitVec.toInt o1) (BitVec.toInt n))) ∧ (∀(d : BitVec 63), BitVec.toInt d = Int.tdiv (BitVec.toInt o1) (BitVec.toInt n) → (let max1 : BitVec 63 := max t1; let marked_old : List Bool := marked t1; (∀(t2 : t), max t2 = max t1 → (∀(p : BitVec 63) (x : ℤ), ((BitVec.toInt n ≤ BitVec.toInt p ∧ BitVec.toInt p ≤ BitVec.toInt max1) ∧ ((3 : ℤ) ≤ BitVec.toInt n ∧ BitVec.toInt n ≤ BitVec.toInt max1) ∧ BitVec.toInt p % (2 : ℤ) = (1 : ℤ) ∧ (BitVec.toInt p ≤ x ∧ x < (nexts t2)[Int.toNat (BitVec.toInt p)]!) ∧ (nexts t2)[Int.toNat x]! = (nexts t2)[Int.toNat (BitVec.toInt p)]! ∧ (marked t2)[Int.toNat (BitVec.toInt n * BitVec.toInt n)]! = true) ∧ EulerSieveSpec.inv_remove_products (nexts t2) (marked t2) (BitVec.toInt n) ∧ EulerSieveSpec.previously_marked_multiples (marked t2) (BitVec.toInt n) ∧ ¬(marked t2)[Int.toNat (BitVec.toInt p)]! = true ∧ EulerSieveSpec.is_copy (marked t2) marked_old ∧ EulerSieveSpec.all_eliminated_marked_partial marked_old (nexts t2) x ∧ EulerSieveSpec.not_marked_impl_next_not_marked marked_old (nexts t2) (BitVec.toInt n) ∧ EulerSieveSpec.prime_multiples_marked marked_old (marked t2) (BitVec.toInt n) ((nexts t2)[Int.toNat x]!) ∧ EulerSieveSpec.not_marked_impl_next_not_marked_partial (marked t2) (nexts t2) (BitVec.toInt n) (BitVec.toInt p) ∧ EulerSieveSpec.only_multiples_marked (marked t2) (BitVec.toInt n + (1 : ℤ)) → (((3 : ℤ) ≤ BitVec.toInt p ∧ BitVec.toInt p ≤ BitVec.toInt (max t2)) ∧ BitVec.toInt p % (2 : ℤ) = (1 : ℤ)) ∧ (∀(next : BitVec 63), ((3 : ℤ) ≤ BitVec.toInt next ∧ BitVec.toInt next ≤ BitVec.toInt (max t2) + (1 : ℤ)) ∧ BitVec.toInt next = (nexts t2)[Int.toNat (BitVec.toInt p)]! ∧ (BitVec.toInt next % (2 : ℤ) = (1 : ℤ) ∨ BitVec.toInt next = BitVec.toInt (max t2) + (1 : ℤ)) → (∀(o2 : Bool), (if (0 : ℤ) ≤ BitVec.toInt next then let o3 : BitVec 63 := max t2; (2 : ℤ) ≤ BitVec.toInt o3 ∧ o2 = (if BitVec.toInt next ≤ BitVec.toInt o3 then true else false) else o2 = false) → (if o2 = true then if BitVec.toInt next ≤ BitVec.toInt d then int'63_in_bounds (BitVec.toInt n * BitVec.toInt next) ∧ (∀(o3 : BitVec 63), BitVec.toInt o3 = BitVec.toInt n * BitVec.toInt next → (((0 : ℤ) ≤ BitVec.toInt o3 ∧ BitVec.toInt o3 ≤ BitVec.toInt (max t2)) ∧ BitVec.toInt o3 % (2 : ℤ) = (1 : ℤ)) ∧ (∀(t3 : t), nexts t3 = nexts t2 ∧ max t3 = max t2 → marked t3 = List.set (marked t2) (Int.toNat (BitVec.toInt o3)) true → (((0 : ℤ) ≤ BitVec.toInt next ∧ BitVec.toInt next ≤ BitVec.toInt (max t3)) ∧ BitVec.toInt next % (2 : ℤ) = (1 : ℤ)) ∧ (if (marked t3)[Int.toNat (BitVec.toInt next)]! = true then (((3 : ℤ) ≤ BitVec.toInt next ∧ BitVec.toInt next ≤ BitVec.toInt (max t3)) ∧ BitVec.toInt next % (2 : ℤ) = (1 : ℤ)) ∧ (∀(o4 : BitVec 63), ((3 : ℤ) ≤ BitVec.toInt o4 ∧ BitVec.toInt o4 ≤ BitVec.toInt (max t3) + (1 : ℤ)) ∧ BitVec.toInt o4 = (nexts t3)[Int.toNat (BitVec.toInt next)]! ∧ (BitVec.toInt o4 % (2 : ℤ) = (1 : ℤ) ∨ BitVec.toInt o4 = BitVec.toInt (max t3) + (1 : ℤ)) → ((((0 : ℤ) ≤ BitVec.toInt p ∧ BitVec.toInt p ≤ BitVec.toInt (max t3)) ∧ BitVec.toInt p < BitVec.toInt o4 ∧ BitVec.toInt o4 ≤ BitVec.toInt (max t3) + (1 : ℤ)) ∧ BitVec.toInt p % (2 : ℤ) = (1 : ℤ) ∧ (∀(j : ℤ), BitVec.toInt p < j ∧ j < BitVec.toInt o4 → (marked t3)[Int.toNat j]! = true) ∧ ¬(marked t3)[Int.toNat (BitVec.toInt p)]! = true ∧ (BitVec.toInt o4 % (2 : ℤ) = (1 : ℤ) ∨ BitVec.toInt o4 = BitVec.toInt (max t3) + (1 : ℤ))) ∧ (∀(t4 : t), marked t4 = marked t3 ∧ max t4 = max t3 → nexts t4 = List.set (nexts t3) (Int.toNat (BitVec.toInt p)) (BitVec.toInt o4) → (let o5 : ℤ := BitVec.toInt next; ((0 : ℤ) ≤ BitVec.toInt max1 - (nexts t2)[Int.toNat (BitVec.toInt p)]! ∧ BitVec.toInt max1 - (nexts t4)[Int.toNat (BitVec.toInt p)]! < BitVec.toInt max1 - (nexts t2)[Int.toNat (BitVec.toInt p)]!) ∧ ((BitVec.toInt n ≤ BitVec.toInt p ∧ BitVec.toInt p ≤ BitVec.toInt max1) ∧ ((3 : ℤ) ≤ BitVec.toInt n ∧ BitVec.toInt n ≤ BitVec.toInt max1) ∧ BitVec.toInt p % (2 : ℤ) = (1 : ℤ) ∧ (BitVec.toInt p ≤ o5 ∧ o5 < (nexts t4)[Int.toNat (BitVec.toInt p)]!) ∧ (nexts t4)[Int.toNat o5]! = (nexts t4)[Int.toNat (BitVec.toInt p)]! ∧ (marked t4)[Int.toNat (BitVec.toInt n * BitVec.toInt n)]! = true) ∧ EulerSieveSpec.inv_remove_products (nexts t4) (marked t4) (BitVec.toInt n) ∧ EulerSieveSpec.previously_marked_multiples (marked t4) (BitVec.toInt n) ∧ ¬(marked t4)[Int.toNat (BitVec.toInt p)]! = true ∧ EulerSieveSpec.is_copy (marked t4) marked_old ∧ EulerSieveSpec.all_eliminated_marked_partial marked_old (nexts t4) o5 ∧ EulerSieveSpec.not_marked_impl_next_not_marked marked_old (nexts t4) (BitVec.toInt n) ∧ EulerSieveSpec.prime_multiples_marked marked_old (marked t4) (BitVec.toInt n) ((nexts t4)[Int.toNat o5]!) ∧ EulerSieveSpec.not_marked_impl_next_not_marked_partial (marked t4) (nexts t4) (BitVec.toInt n) (BitVec.toInt p) ∧ EulerSieveSpec.only_multiples_marked (marked t4) (BitVec.toInt n + (1 : ℤ))))) else let o4 : ℤ := BitVec.toInt next; ((0 : ℤ) ≤ BitVec.toInt max1 - (nexts t2)[Int.toNat (BitVec.toInt p)]! ∧ BitVec.toInt max1 - (nexts t3)[Int.toNat (BitVec.toInt next)]! < BitVec.toInt max1 - (nexts t2)[Int.toNat (BitVec.toInt p)]!) ∧ ((BitVec.toInt n ≤ BitVec.toInt next ∧ BitVec.toInt next ≤ BitVec.toInt max1) ∧ ((3 : ℤ) ≤ BitVec.toInt n ∧ BitVec.toInt n ≤ BitVec.toInt max1) ∧ BitVec.toInt next % (2 : ℤ) = (1 : ℤ) ∧ (BitVec.toInt next ≤ o4 ∧ o4 < (nexts t3)[Int.toNat (BitVec.toInt next)]!) ∧ (nexts t3)[Int.toNat o4]! = (nexts t3)[Int.toNat (BitVec.toInt next)]! ∧ (marked t3)[Int.toNat (BitVec.toInt n * BitVec.toInt n)]! = true) ∧ EulerSieveSpec.inv_remove_products (nexts t3) (marked t3) (BitVec.toInt n) ∧ EulerSieveSpec.previously_marked_multiples (marked t3) (BitVec.toInt n) ∧ ¬(marked t3)[Int.toNat (BitVec.toInt next)]! = true ∧ EulerSieveSpec.is_copy (marked t3) marked_old ∧ EulerSieveSpec.all_eliminated_marked_partial marked_old (nexts t3) o4 ∧ EulerSieveSpec.not_marked_impl_next_not_marked marked_old (nexts t3) (BitVec.toInt n) ∧ EulerSieveSpec.prime_multiples_marked marked_old (marked t3) (BitVec.toInt n) ((nexts t3)[Int.toNat o4]!) ∧ EulerSieveSpec.not_marked_impl_next_not_marked_partial (marked t3) (nexts t3) (BitVec.toInt n) (BitVec.toInt next) ∧ EulerSieveSpec.only_multiples_marked (marked t3) (BitVec.toInt n + (1 : ℤ))))) else EulerSieveSpec.inv_remove_products (nexts t2) (marked t2) (BitVec.toInt n) ∧ EulerSieveSpec.not_marked_impl_next_not_marked (marked t2) (nexts t2) ((nexts t2)[Int.toNat (BitVec.toInt n)]!) ∧ EulerSieveSpec.is_copy (marked t2) marked_old ∧ EulerSieveSpec.previously_marked_multiples (marked t2) (BitVec.toInt n) ∧ EulerSieveSpec.prime_multiples_marked marked_old (marked t2) (BitVec.toInt n) (Int.ofNat (List.length (marked t2))) ∧ EulerSieveSpec.only_multiples_marked (marked t2) (BitVec.toInt n + (1 : ℤ)) else EulerSieveSpec.inv_remove_products (nexts t2) (marked t2) (BitVec.toInt n) ∧ EulerSieveSpec.not_marked_impl_next_not_marked (marked t2) (nexts t2) ((nexts t2)[Int.toNat (BitVec.toInt n)]!) ∧ EulerSieveSpec.is_copy (marked t2) marked_old ∧ EulerSieveSpec.previously_marked_multiples (marked t2) (BitVec.toInt n) ∧ EulerSieveSpec.prime_multiples_marked marked_old (marked t2) (BitVec.toInt n) (Int.ofNat (List.length (marked t2))) ∧ EulerSieveSpec.only_multiples_marked (marked t2) (BitVec.toInt n + (1 : ℤ))))))) ∧ int'63_in_bounds (BitVec.toInt n * BitVec.toInt n) ∧ (∀(o2 : BitVec 63), BitVec.toInt o2 = BitVec.toInt n * BitVec.toInt n → (((0 : ℤ) ≤ BitVec.toInt o2 ∧ BitVec.toInt o2 ≤ BitVec.toInt (max t1)) ∧ BitVec.toInt o2 % (2 : ℤ) = (1 : ℤ)) ∧ (∀(t2 : t), nexts t2 = nexts t1 ∧ max t2 = max t1 → marked t2 = List.set (marked t1) (Int.toNat (BitVec.toInt o2)) true → (let o3 : ℤ := BitVec.toInt n; (((BitVec.toInt n ≤ BitVec.toInt n ∧ BitVec.toInt n ≤ BitVec.toInt max1) ∧ ((3 : ℤ) ≤ BitVec.toInt n ∧ BitVec.toInt n ≤ BitVec.toInt max1) ∧ BitVec.toInt n % (2 : ℤ) = (1 : ℤ) ∧ (BitVec.toInt n ≤ o3 ∧ o3 < (nexts t2)[Int.toNat (BitVec.toInt n)]!) ∧ (nexts t2)[Int.toNat o3]! = (nexts t2)[Int.toNat (BitVec.toInt n)]! ∧ (marked t2)[Int.toNat (BitVec.toInt n * BitVec.toInt n)]! = true) ∧ EulerSieveSpec.inv_remove_products (nexts t2) (marked t2) (BitVec.toInt n) ∧ EulerSieveSpec.previously_marked_multiples (marked t2) (BitVec.toInt n) ∧ ¬(marked t2)[Int.toNat (BitVec.toInt n)]! = true ∧ EulerSieveSpec.is_copy (marked t2) marked_old ∧ EulerSieveSpec.all_eliminated_marked_partial marked_old (nexts t2) o3 ∧ EulerSieveSpec.not_marked_impl_next_not_marked marked_old (nexts t2) (BitVec.toInt n) ∧ EulerSieveSpec.prime_multiples_marked marked_old (marked t2) (BitVec.toInt n) ((nexts t2)[Int.toNat o3]!) ∧ EulerSieveSpec.not_marked_impl_next_not_marked_partial (marked t2) (nexts t2) (BitVec.toInt n) (BitVec.toInt n) ∧ EulerSieveSpec.only_multiples_marked (marked t2) (BitVec.toInt n + (1 : ℤ))) ∧ (∀(t3 : t), max t3 = max t2 → EulerSieveSpec.inv_remove_products (nexts t3) (marked t3) (BitVec.toInt n) ∧ EulerSieveSpec.not_marked_impl_next_not_marked (marked t3) (nexts t3) ((nexts t3)[Int.toNat (BitVec.toInt n)]!) ∧ EulerSieveSpec.is_copy (marked t3) marked_old ∧ EulerSieveSpec.previously_marked_multiples (marked t3) (BitVec.toInt n) ∧ EulerSieveSpec.prime_multiples_marked marked_old (marked t3) (BitVec.toInt n) (Int.ofNat (List.length (marked t3))) ∧ EulerSieveSpec.only_multiples_marked (marked t3) (BitVec.toInt n + (1 : ℤ)) → EulerSieveSpec.inv_remove_products (nexts t3) (marked t3) (BitVec.toInt n) ∧ EulerSieveSpec.not_marked_impl_next_not_marked (marked t3) (nexts t3) ((nexts t3)[Int.toNat (BitVec.toInt n)]!) ∧ EulerSieveSpec.previously_marked_multiples (marked t3) ((nexts t3)[Int.toNat (BitVec.toInt n)]!) ∧ EulerSieveSpec.only_multiples_marked (marked t3) ((nexts t3)[Int.toNat (BitVec.toInt n)]!)))))))
  := sorry
end euler_sieve_EulerSieve_remove_productsqtvc
