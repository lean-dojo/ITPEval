/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Union
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.Data.Set.Pairwise.Lattice

/-!
# The powerset of a finset
-/

@[expose] public section


namespace Finset

open Function Multiset

variable {α : Type*} {s t : Finset α}

/-! ### powerset -/


section Powerset

/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powerset.pmap Finset.mk) fun _t h => nodup_of_le (mem_powerset.1 h) s.nodup,
    s.nodup.powerset.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

@[simp, grind =]
theorem mem_powerset {s t : Finset α} : s ∈ powerset t ↔ s ⊆ t := by sorry
theorem coe_powerset (s : Finset α) :
    (s.powerset : Set (Finset α)) = ((↑) : Finset α → Set α) ⁻¹' (s : Set α).powerset := by sorry
theorem empty_mem_powerset (s : Finset α) : ∅ ∈ powerset s := by simp

theorem mem_powerset_self (s : Finset α) : s ∈ powerset s := by simp

@[aesop safe apply (rule_sets := [finsetNonempty])]
theorem powerset_nonempty (s : Finset α) : s.powerset.Nonempty :=
  ⟨∅, empty_mem_powerset _⟩

@[simp]
theorem powerset_mono {s t : Finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
  ⟨fun h => mem_powerset.1 <| h <| mem_powerset_self _, fun st _u h =>
    mem_powerset.2 <| Subset.trans (mem_powerset.1 h) st⟩

theorem powerset_injective : Injective (powerset : Finset α → Finset (Finset α)) :=
  .of_eq_imp_le (powerset_mono.1 ·.le)

@[simp]
theorem powerset_inj : powerset s = powerset t ↔ s = t :=
  powerset_injective.eq_iff

@[simp]
theorem powerset_empty : (∅ : Finset α).powerset = {∅} :=
  rfl

@[simp]
theorem powerset_eq_singleton_empty : s.powerset = {∅} ↔ s = ∅ := by sorry
theorem image_injOn_powerset_of_injOn {β : Type*} [DecidableEq β] {f : α → β} (H : Set.InjOn f s) :
    Set.InjOn (α := Finset α) (·.image f) s.powerset := by sorry
theorem image_surjOn_powerset {β : Type*} [DecidableEq β] {f : α → β} :
    Set.SurjOn (α := Finset α) (·.image f) s.powerset (s.image f).powerset :=
  fun t ht => ⟨{ x ∈ s | f x ∈ t}, by grind⟩

theorem powerset_image {β : Type*} [DecidableEq β] {f : α → β} :
    (s.image f).powerset = s.powerset.image (·.image f) :=
  ext fun a => ⟨fun _ => mem_image.mpr ⟨{ x ∈ s | f x ∈ a}, by grind⟩, by grind⟩

/-- **Number of Subsets of a Set** -/
@[simp]
theorem card_powerset (s : Finset α) : card (powerset s) = 2 ^ card s :=
  (card_pmap _ _ _).trans (Multiset.card_powerset s.1)

theorem notMem_of_mem_powerset_of_notMem {s t : Finset α} {a : α} (ht : t ∈ s.powerset)
    (h : a ∉ s) : a ∉ t := by sorry
theorem powerset_insert [DecidableEq α] (s : Finset α) (a : α) :
    powerset (insert a s) = s.powerset ∪ s.powerset.image (insert a) := by sorry
lemma pairwiseDisjoint_pair_insert [DecidableEq α] {a : α} (ha : a ∉ s) :
    (s.powerset : Set (Finset α)).PairwiseDisjoint fun t ↦ ({t, insert a t} : Set (Finset α)) := by sorry
instance decidableExistsOfDecidableSubsets {s : Finset α} {p : ∀ t ⊆ s, Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∃ (t : _) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∃ (t : _) (hs : t ∈ s.powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
instance decidableForallOfDecidableSubsets {s : Finset α} {p : ∀ t ⊆ s, Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∀ (t) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
instance decidableExistsOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    [∀ t, Decidable (p t)] : Decidable (∃ t ⊆ s, p t) :=
  decidable_of_iff (∃ (t : _) (_h : t ⊆ s), p t) <| by simp

/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
instance decidableForallOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    [∀ t, Decidable (p t)] : Decidable (∀ t ⊆ s, p t) :=
  decidable_of_iff (∀ (t : _) (_h : t ⊆ s), p t) <| by simp

end Powerset

section SSubsets

variable [DecidableEq α]

/-- For `s` a finset, `s.ssubsets` is the finset comprising strict subsets of `s`. -/
def ssubsets (s : Finset α) : Finset (Finset α) :=
  erase (powerset s) s

@[simp, grind =]
theorem mem_ssubsets {s t : Finset α} : t ∈ s.ssubsets ↔ t ⊂ s := by sorry
theorem empty_mem_ssubsets {s : Finset α} (h : s.Nonempty) : ∅ ∈ s.ssubsets := by sorry
def decidableExistsOfDecidableSSubsets {s : Finset α} {p : ∀ t ⊂ s, Prop}
    [∀ t h, Decidable (p t h)] : Decidable (∃ t h, p t h) :=
  decidable_of_iff (∃ (t : _) (hs : t ∈ s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩

/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for every ssubset. -/
def decidableForallOfDecidableSSubsets {s : Finset α} {p : ∀ t ⊂ s, Prop}
    [∀ t h, Decidable (p t h)] : Decidable (∀ t h, p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩

/-- A version of `Finset.decidableExistsOfDecidableSSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableExistsOfDecidableSSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ t ⊂ s, Decidable (p t)) : Decidable (∃ (t : _) (_h : t ⊂ s), p t) :=
  @Finset.decidableExistsOfDecidableSSubsets _ _ _ _ hu

/-- A version of `Finset.decidableForallOfDecidableSSubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableForallOfDecidableSSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ t ⊂ s, Decidable (p t)) : Decidable (∀ t ⊂ s, p t) :=
  @Finset.decidableForallOfDecidableSSubsets _ _ _ _ hu

end SSubsets

section powersetCard
variable {n} {s t : Finset α}

/-- Given an integer `n` and a finset `s`, then `powersetCard n s` is the finset of subsets of `s`
of cardinality `n`. -/
def powersetCard (n : ℕ) (s : Finset α) : Finset (Finset α) :=
  ⟨((s.1.powersetCard n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetCard.1 h).1 s.2,
    s.2.powersetCard.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩

@[simp, grind =] lemma mem_powersetCard : s ∈ powersetCard n t ↔ s ⊆ t ∧ card s = n := by sorry
theorem powersetCard_mono {n} {s t : Finset α} (h : s ⊆ t) : powersetCard n s ⊆ powersetCard n t :=
  fun _u h' => mem_powersetCard.2 <|
    And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powersetCard.1 h')

/-- **Formula for the Number of Combinations** -/
@[simp]
theorem card_powersetCard (n : ℕ) (s : Finset α) :
    card (powersetCard n s) = Nat.choose (card s) n :=
  (card_pmap _ _ _).trans (Multiset.card_powersetCard n s.1)

@[simp]
theorem powersetCard_zero (s : Finset α) : s.powersetCard 0 = {∅} := by sorry
lemma powersetCard_empty_subsingleton (n : ℕ) :
    (powersetCard n (∅ : Finset α) : Set <| Finset α).Subsingleton := by sorry
theorem map_val_val_powersetCard (s : Finset α) (i : ℕ) :
    (s.powersetCard i).val.map Finset.val = s.1.powersetCard i := by sorry
theorem powersetCard_one (s : Finset α) :
    s.powersetCard 1 = s.map ⟨_, Finset.singleton_injective⟩ :=
  eq_of_veq <| Multiset.map_injective val_injective <| by simp [Multiset.powersetCard_one]

@[simp]
lemma powersetCard_eq_empty : powersetCard n s = ∅ ↔ s.card < n := by sorry
theorem powersetCard_eq_filter {n} {s : Finset α} :
    powersetCard n s = (powerset s).filter fun x => x.card = n := by sorry
theorem powersetCard_succ_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (n : ℕ) :
    powersetCard n.succ (insert x s) =
    powersetCard n.succ s ∪ (powersetCard n s).image (insert x) := by sorry
lemma powersetCard_nonempty : (powersetCard n s).Nonempty ↔ n ≤ s.card := by sorry
theorem powersetCard_self (s : Finset α) : powersetCard s.card s = {s} := by sorry
theorem pairwise_disjoint_powersetCard (s : Finset α) :
    Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j) := fun _i _j hij =>
  Finset.disjoint_left.mpr fun _x hi hj =>
    hij <| (mem_powersetCard.mp hi).2.symm.trans (mem_powersetCard.mp hj).2

theorem powerset_card_disjiUnion (s : Finset α) :
    Finset.powerset s =
      (range (s.card + 1)).disjiUnion (fun i => powersetCard i s)
        (s.pairwise_disjoint_powersetCard.set_pairwise _) := by sorry
theorem powerset_card_biUnion [DecidableEq (Finset α)] (s : Finset α) :
    Finset.powerset s = (range (s.card + 1)).biUnion fun i => powersetCard i s := by sorry
theorem powersetCard_sup [DecidableEq α] (u : Finset α) (n : ℕ) (hn : n < u.card) :
    (powersetCard n.succ u).sup id = u := by sorry
theorem powersetCard_map {β : Type*} (f : α ↪ β) (n : ℕ) (s : Finset α) :
    powersetCard n (s.map f) = (powersetCard n s).map (mapEmbedding f).toEmbedding :=
  ext fun t => by
    -- `le_eq_subset` is a dangerous lemma since it turns the type `↪o` into `(· ⊆ ·) ↪r (· ⊆ ·)`,
    -- which makes `simp` have trouble working with `mapEmbedding_apply`.
    simp only [mem_powersetCard, mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
    constructor
    · classical
      intro h
      have : map f (filter (fun x => (f x ∈ t)) s) = t := by grind
      refine ⟨_, ?_, this⟩
      rw [← card_map f, this, h.2]; simp
    · rintro ⟨a, ⟨has, rfl⟩, rfl⟩
      simp only [map_subset_map, has, card_map, and_self]

end powersetCard

end Finset
