/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

## Main definitions

* `Sylow p G` : The type of Sylow `p`-subgroups of `G`.

## Main statements

* `Sylow.exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `IsPGroup.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `Sylow.card_eq_multiplicity`: The cardinality of a Sylow subgroup is `p ^ n`
  where `n` is the multiplicity of `p` in the group order.
* `Sylow.isPretransitive_of_finite`: a generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modEq_one`: a generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/

@[expose] public section


open MulAction Subgroup

section InfiniteSylow

variable (p : ℕ) (G : Type*) [Group G]

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure Sylow extends Subgroup G where
  isPGroup' : IsPGroup p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G}, IsPGroup p Q → toSubgroup ≤ Q → Q = toSubgroup

variable {p} {G}

namespace Sylow

attribute [coe] toSubgroup

instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨toSubgroup⟩

@[ext]
theorem ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q := by cases P; cases Q; congr

instance : SetLike (Sylow p G) G where
  coe := (↑)
  coe_injective' _ _ h := ext (SetLike.coe_injective h)

instance : PartialOrder (Sylow p G) := .ofSetLike (Sylow p G) G

instance : SubgroupClass (Sylow p G) G where
  mul_mem := Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _

@[simp]
protected theorem coe_coe (P : Sylow p G) : (P : Subgroup G) = (P : Set G) :=
  rfl

/-- A `p`-subgroup with index indivisible by `p` is a Sylow subgroup. -/
def _root_.IsPGroup.toSylow [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : Sylow p G :=
  { P with
    isPGroup' := hP1
    is_maximal' := by sorry
def ofCard [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : Sylow p G :=
  (IsPGroup.of_card card_eq).toSylow (by
    rw [← mul_dvd_mul_iff_left (Nat.card_pos (α := H)).ne', card_mul_index, card_eq, ← pow_succ]
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Fact.out)

@[simp, norm_cast]
theorem coe_ofCard [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : ofCard H card_eq = H :=
  rfl

variable (P : Sylow p G)

variable {K : Type*} [Group K] (ϕ : K →* G) {N : Subgroup G}

/-- The preimage of a Sylow subgroup under a p-group-kernel homomorphism is a Sylow subgroup. -/
def comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P ≤ ϕ.range) : Sylow p K :=
  { P.1.comap ϕ with
    isPGroup' := P.2.comap_of_ker_isPGroup ϕ hϕ
    is_maximal' := fun {Q} hQ hle => by
      show Q = P.1.comap ϕ
      rw [← P.3 (hQ.map ϕ) (le_trans (ge_of_eq (map_comap_eq_self h)) (map_mono hle))]
      exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }

@[simp]
theorem coe_comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P ≤ ϕ.range) :
    P.comapOfKerIsPGroup ϕ hϕ h = P.comap ϕ :=
  rfl

/-- The preimage of a Sylow subgroup under an injective homomorphism is a Sylow subgroup. -/
def comapOfInjective (hϕ : Function.Injective ϕ) (h : P ≤ ϕ.range) : Sylow p K :=
  P.comapOfKerIsPGroup ϕ (IsPGroup.ker_isPGroup_of_injective hϕ) h

@[simp]
theorem coe_comapOfInjective (hϕ : Function.Injective ϕ) (h : P ≤ ϕ.range) :
    P.comapOfInjective ϕ hϕ h = P.comap ϕ :=
  rfl

/-- A sylow subgroup of G is also a sylow subgroup of a subgroup of G. -/
protected def subtype (h : P ≤ N) : Sylow p N :=
  P.comapOfInjective N.subtype Subtype.coe_injective (by rwa [range_subtype])

@[simp]
theorem coe_subtype (h : P ≤ N) : P.subtype h = subgroupOf P N :=
  rfl

theorem subtype_injective {P Q : Sylow p G} {hP : P ≤ N} {hQ : Q ≤ N}
    (h : P.subtype hP = Q.subtype hQ) : P = Q := by sorry
end Sylow

/-- A generalization of **Sylow's first theorem**.
  Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/
theorem IsPGroup.exists_le_sylow {P : Subgroup G} (hP : IsPGroup p P) : ∃ Q : Sylow p G, P ≤ Q :=
  Exists.elim
    (zorn_le_nonempty₀ { Q : Subgroup G | IsPGroup p Q }
      (fun c hc1 hc2 Q hQ =>
        ⟨{  carrier := ⋃ R : c, R
            one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩
            inv_mem' := fun {_} ⟨_, ⟨R, rfl⟩, hg⟩ => ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩
            mul_mem' := fun {_} _ ⟨_, ⟨R, rfl⟩, hg⟩ ⟨_, ⟨S, rfl⟩, hh⟩ =>
              (hc2.total R.2 S.2).elim (fun T => ⟨S, ⟨S, rfl⟩, S.1.mul_mem (T hg) hh⟩) fun T =>
                ⟨R, ⟨R, rfl⟩, R.1.mul_mem hg (T hh)⟩ },
          fun ⟨g, _, ⟨S, rfl⟩, hg⟩ => by
          refine Exists.imp (fun k hk => ?_) (hc1 S.2 ⟨g, hg⟩)
          rwa [Subtype.ext_iff, coe_pow] at hk ⊢, fun M hM _ hg => ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩)
      P hP)
    fun {Q} h => ⟨⟨Q, h.2.prop, h.2.eq_of_ge⟩, h.1⟩

namespace Sylow

instance nonempty : Nonempty (Sylow p G) :=
  IsPGroup.of_bot.exists_le_sylow.nonempty

noncomputable instance inhabited : Inhabited (Sylow p G) :=
  Classical.inhabited_of_nonempty nonempty

theorem exists_comap_eq_of_ker_isPGroup {H : Type*} [Group H] (P : Sylow p H) {f : H →* G}
    (hf : IsPGroup p f.ker) : ∃ Q : Sylow p G, Q.comap f = P :=
  Exists.imp (fun Q hQ => P.3 (Q.2.comap_of_ker_isPGroup f hf) (map_le_iff_le_comap.mp hQ))
    (P.2.map f).exists_le_sylow

theorem exists_comap_eq_of_injective {H : Type*} [Group H] (P : Sylow p H) {f : H →* G}
    (hf : Function.Injective f) : ∃ Q : Sylow p G, Q.comap f = P :=
  P.exists_comap_eq_of_ker_isPGroup (IsPGroup.ker_isPGroup_of_injective hf)

theorem exists_comap_subtype_eq {H : Subgroup G} (P : Sylow p H) :
    ∃ Q : Sylow p G, Q.comap H.subtype = P :=
  P.exists_comap_eq_of_injective Subtype.coe_injective

/-- If the kernel of `f : H →* G` is a `p`-group,
  then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
theorem finite_of_ker_is_pGroup {H : Type*} [Group H] {f : H →* G}
    (hf : IsPGroup p f.ker) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  let h_exists := fun P : Sylow p H => P.exists_comap_eq_of_ker_isPGroup hf
  let g : Sylow p H → Sylow p G := fun P => Classical.choose (h_exists P)
  have hg : ∀ P : Sylow p H, (g P).1.comap f = P := fun P => Classical.choose_spec (h_exists P)
  Finite.of_injective g fun P Q h => ext (by rw [← hg, h]; exact (h_exists Q).choose_spec)

/-- If `f : H →* G` is injective, then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
theorem finite_of_injective {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Injective f) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  finite_of_ker_is_pGroup (IsPGroup.ker_isPGroup_of_injective hf)

/-- If `H` is a subgroup of `G`, then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
instance (H : Subgroup G) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  finite_of_injective H.subtype_injective

/-- If a Sylow `p`-subgroup has finite index, then the number of Sylow `p`-subgroups is finite. -/
theorem finite_of_finiteIndex (P : Sylow p G) [P.FiniteIndex] : Finite (Sylow p G) := by sorry
open Pointwise

/-- `Subgroup.pointwiseMulAction` preserves Sylow subgroups. -/
instance pointwiseMulAction {α : Type*} [Group α] [MulDistribMulAction α G] :
    MulAction α (Sylow p G) where
  smul g P :=
    ⟨g • P.toSubgroup, P.2.map _, fun {Q} hQ hS =>
      inv_smul_eq_iff.mp
        (P.3 (hQ.map _) fun s hs =>
          (congr_arg (· ∈ g⁻¹ • Q) (inv_smul_smul g s)).mp
            (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs))))⟩
  one_smul P := ext (one_smul α P.toSubgroup)
  mul_smul g h P := ext (mul_smul g h P.toSubgroup)

theorem pointwise_smul_def {α : Type*} [Group α] [MulDistribMulAction α G] {g : α}
    {P : Sylow p G} : ↑(g • P) = g • (P : Subgroup G) :=
  rfl

instance mulAction : MulAction G (Sylow p G) :=
  compHom _ MulAut.conj

theorem smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g • P :=
  rfl

theorem coe_subgroup_smul {g : G} {P : Sylow p G} :
    ↑(g • P) = MulAut.conj g • (P : Subgroup G) :=
  rfl

theorem coe_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Set G) :=
  rfl

theorem smul_le {P : Sylow p G} {H : Subgroup G} (hP : P ≤ H) (h : H) : ↑(h • P) ≤ H :=
  Subgroup.conj_smul_le_of_le hP h

theorem smul_subtype {P : Sylow p G} {H : Subgroup G} (hP : P ≤ H) (h : H) :
    h • P.subtype hP = (h • P).subtype (smul_le hP h) :=
  ext (Subgroup.conj_smul_subgroupOf hP h)

theorem smul_eq_iff_mem_normalizer {g : G} {P : Sylow p G} :
    g • P = P ↔ g ∈ normalizer P := by sorry
theorem smul_eq_of_normal {g : G} {P : Sylow p G} [h : P.Normal] : g • P = P := by sorry
end Sylow

theorem Subgroup.sylow_mem_fixedPoints_iff (H : Subgroup G) {P : Sylow p G} :
    P ∈ fixedPoints H (Sylow p G) ↔ H ≤ normalizer P := by sorry
theorem IsPGroup.inf_normalizer_sylow {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G) :
    P ⊓ normalizer Q = P ⊓ Q :=
  le_antisymm
    (le_inf inf_le_left
      (sup_eq_right.mp
        (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)

theorem IsPGroup.sylow_mem_fixedPoints_iff {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} :
    Q ∈ fixedPoints P (Sylow p G) ↔ P ≤ Q := by sorry
instance Sylow.isPretransitive_of_finite [hp : Fact p.Prime] [Finite (Sylow p G)] :
    IsPretransitive G (Sylow p G) :=
  ⟨fun P Q => by
    classical
      have H := fun {R : Sylow p G} {S : orbit G P} =>
        calc
          S ∈ fixedPoints R (orbit G P) ↔ S.1 ∈ fixedPoints R (Sylow p G) :=
            forall_congr' fun a => Subtype.ext_iff
          _ ↔ R.1 ≤ S := R.2.sylow_mem_fixedPoints_iff
          _ ↔ S.1.1 = R := ⟨fun h => R.3 S.1.2 h, ge_of_eq⟩
      suffices Set.Nonempty (fixedPoints Q (orbit G P)) by
        exact Exists.elim this fun R hR => by
          rw [← Sylow.ext (H.mp hR)]
          exact R.2
      apply Q.2.nonempty_fixed_point_of_prime_not_dvd_card
      refine fun h => hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.mp ?_)
      calc
        1 = Nat.card (fixedPoints P (orbit G P)) := ?_
        _ ≡ Nat.card (orbit G P) [MOD p] := (P.2.card_modEq_card_fixedPoints (orbit G P)).symm
        _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
      rw [← Nat.card_unique (α := ({⟨P, mem_orbit_self P⟩} : Set (orbit G P))), eq_comm]
      congr
      rw [Set.eq_singleton_iff_unique_mem]
      exact ⟨H.mpr rfl, fun R h => Subtype.ext (Sylow.ext (H.mp h))⟩⟩

variable (p) (G)

/-- A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`. -/
theorem card_sylow_modEq_one [Fact p.Prime] [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] := by sorry
theorem not_dvd_card_sylow [hp : Fact p.Prime] [Finite (Sylow p G)] : ¬p ∣ Nat.card (Sylow p G) :=
  fun h =>
  hp.1.ne_one
    (Nat.dvd_one.mp
      ((Nat.modEq_iff_dvd' zero_le_one).mp
        ((Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p G))))

variable {p} {G}

namespace Sylow

/-- Sylow subgroups are isomorphic -/
nonrec def equivSMul (P : Sylow p G) (g : G) : P ≃* (g • P : Sylow p G) :=
  equivSMul (MulAut.conj g) P.toSubgroup

/-- Sylow subgroups are isomorphic -/
noncomputable def equiv [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G) : P ≃* Q := by sorry
theorem orbit_eq_top [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : orbit G P = ⊤ :=
  top_le_iff.mp fun Q _ => exists_smul_eq G P Q

theorem stabilizer_eq_normalizer (P : Sylow p G) :
    stabilizer G P = normalizer P := by sorry
theorem conj_eq_normalizer_conj_of_mem_centralizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) (x g : G) (hx : x ∈ centralizer P)
    (hy : g⁻¹ * x * g ∈ centralizer P) :
    ∃ n ∈ normalizer P, g⁻¹ * x * g = n⁻¹ * x * n := by sorry
theorem conj_eq_normalizer_conj_of_mem [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    [_hP : IsMulCommutative P] (x g : G) (hx : x ∈ P) (hy : g⁻¹ * x * g ∈ P) :
    ∃ n ∈ normalizer P, g⁻¹ * x * g = n⁻¹ * x * n :=
  P.conj_eq_normalizer_conj_of_mem_centralizer x g
    (P.le_centralizer hx) (P.le_centralizer hy)

/-- Sylow `p`-subgroups are in bijection with cosets of the normalizer of a Sylow `p`-subgroup -/
noncomputable def equivQuotientNormalizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : Sylow p G ≃ G ⧸ normalizer P :=
  calc
    Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equiv.Set.univ (Sylow p G)).symm
    _ ≃ orbit G P := Equiv.setCongr P.orbit_eq_top.symm
    _ ≃ G ⧸ stabilizer G P := orbitEquivQuotientStabilizer G P
    _ ≃ G ⧸ normalizer P := by rw [P.stabilizer_eq_normalizer]

instance [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Finite (G ⧸ normalizer P) :=
  Finite.of_equiv (Sylow p G) P.equivQuotientNormalizer

theorem card_eq_card_quotient_normalizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : Nat.card (Sylow p G) = Nat.card (G ⧸ normalizer P) :=
  Nat.card_congr P.equivQuotientNormalizer

theorem card_eq_index_normalizer [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) = (normalizer (P : Set G)).index :=
  P.card_eq_card_quotient_normalizer

theorem card_dvd_index [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.index :=
  ((congr_arg _ P.card_eq_index_normalizer).mp dvd_rfl).trans
    (index_dvd_of_le le_normalizer)

/-- Auxiliary lemma for `Sylow.not_dvd_index` which is strictly stronger. -/
private theorem not_dvd_index_aux [hp : Fact p.Prime] (P : Sylow p G) [P.Normal]
    [P.FiniteIndex] : ¬ p ∣ P.index := by sorry
theorem not_dvd_index' [hp : Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hP : P.relIndex (normalizer P) ≠ 0) : ¬ p ∣ P.index := by sorry
theorem not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex] :
    ¬ p ∣ P.index := by sorry
section mapSurjective

variable [Finite G] {G' : Type*} [Group G'] {f : G →* G'} (hf : Function.Surjective f)

/-- Surjective group homomorphisms map Sylow subgroups to Sylow subgroups. -/
def mapSurjective [Fact p.Prime] (P : Sylow p G) : Sylow p G' :=
  { P.1.map f with
    isPGroup' := P.2.map f
    is_maximal' := fun hQ hPQ ↦ ((P.2.map f).toSylow
      (fun h ↦ P.not_dvd_index (h.trans (P.index_map_dvd hf)))).3 hQ hPQ }

@[simp] theorem coe_mapSurjective [Fact p.Prime] (P : Sylow p G) : P.mapSurjective hf = P.map f :=
  rfl

theorem mapSurjective_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (Sylow.mapSurjective hf : Sylow p G → Sylow p G') := by sorry
end mapSurjective

/-- **Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
theorem normalizer_sup_eq_top {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p N) :
    normalizer (P.map N.subtype) ⊔ N = ⊤ := by sorry
theorem normalizer_sup_eq_top' {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p G) (hP : P ≤ N) : normalizer P ⊔ N = ⊤ := by sorry
end Sylow

end InfiniteSylow

open Equiv Equiv.Perm Finset Function List QuotientGroup

universe u

variable {G : Type u} [Group G]

theorem QuotientGroup.card_preimage_mk (s : Subgroup G) (t : Set (G ⧸ s)) :
    Nat.card (QuotientGroup.mk ⁻¹' t) = Nat.card s * Nat.card t := by sorry
namespace Sylow
theorem mem_fixedPoints_mul_left_cosets_iff_mem_normalizer {H : Subgroup G} [Finite (H : Set G)]
    {x : G} : (x : G ⧸ H) ∈ MulAction.fixedPoints H (G ⧸ H) ↔ x ∈ normalizer H :=
  ⟨fun hx =>
    have ha : ∀ {y : G ⧸ H}, y ∈ orbit H (x : G ⧸ H) → y = x := mem_fixedPoints'.1 hx _
    (inv_mem_iff (G := G)).1
      (mem_normalizer_fintype fun n (hn : n ∈ H) =>
        have : (n⁻¹ * x)⁻¹ * x ∈ H := QuotientGroup.eq.1 (ha ⟨⟨n⁻¹, inv_mem hn⟩, rfl⟩)
        show _ ∈ H by
          rw [mul_inv_rev, inv_inv] at this
          convert this
          rw [inv_inv]),
    fun hx : ∀ n : G, n ∈ H ↔ x * n * x⁻¹ ∈ H =>
    mem_fixedPoints'.2 fun y =>
      Quotient.inductionOn' y fun y hy =>
        QuotientGroup.eq.2
          (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy
          have hb₂ : (b * x)⁻¹ * y ∈ H := QuotientGroup.eq.1 hb₂
          (inv_mem_iff (G := G)).1 <|
            (hx _).2 <|
              (mul_mem_cancel_left (inv_mem hb₁)).1 <| by
                rw [hx] at hb₂; simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

/-- The fixed points of the action of `H` on its cosets correspond to `normalizer H / H`. -/
def fixedPointsMulLeftCosetsEquivQuotient (H : Subgroup G) [Finite (H : Set G)] :
    MulAction.fixedPoints H (G ⧸ H) ≃
      normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype :=
  @subtypeQuotientEquivQuotientSubtype G (· ∈ normalizer H) (_) (_)
    (· ∈ MulAction.fixedPoints H (G ⧸ H))
    (fun _ => (@mem_fixedPoints_mul_left_cosets_iff_mem_normalizer _ _ _ ‹_› _).symm)
    (by
      intros
      unfold_projs
      rw [leftRel_apply (α := normalizer (H : Set G)), leftRel_apply]
      rfl)

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`. -/
theorem card_quotient_normalizer_modEq_card_quotient [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    Nat.card (normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype) ≡
      Nat.card (G ⧸ H) [MOD p] := by sorry
theorem card_normalizer_modEq_card [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] {H : Subgroup G}
    (hH : Nat.card H = p ^ n) :
    Nat.card (normalizer (H : Set G)) ≡ Nat.card G [MOD p ^ (n + 1)] := by sorry
theorem prime_dvd_card_quotient_normalizer [Finite G] {p : ℕ} {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    p ∣ Nat.card (normalizer (H : Set G) ⧸ H.comap (normalizer (H : Set G)).subtype) :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H ≠ 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ', mul_assoc, mul_comm p])
  have hm :
    s * p % p =
      Nat.card (normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype) % p :=
    hcard ▸ (card_quotient_normalizer_modEq_card_quotient hH).symm
  Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
theorem prime_pow_dvd_card_normalizer [Finite G] {p : ℕ} {n : ℕ} [_hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    p ^ (n + 1) ∣ Nat.card (normalizer (H : Set G)) :=
  Nat.modEq_zero_iff_dvd.1 ((card_normalizer_modEq_card hH).trans hdvd.modEq_zero_nat)

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    ∃ K : Subgroup G, Nat.card K = p ^ (n + 1) ∧ H ≤ K :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H ≠ 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ', mul_assoc, mul_comm p])
  have hm : s * p % p = Nat.card (normalizer H ⧸ H.subgroupOf (normalizer H)) % p :=
    Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H) ▸
      hcard ▸ (IsPGroup.of_card hH).card_modEq_card_fixedPoints _
  have hm' : p ∣ Nat.card (normalizer H ⧸ H.subgroupOf (normalizer H)) :=
    Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)
  let ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' _ (QuotientGroup.Quotient.group _) _ _ hp hm'
  have hequiv : H ≃ H.subgroupOf (normalizer H) := (subgroupOfEquivOfLe le_normalizer).symm.toEquiv
  ⟨((zpowers x).comap (mk' (H.subgroupOf (normalizer H)))).map (normalizer H).subtype, by
    show Nat.card (Subgroup.map (normalizer (H : Set G)).subtype
      (comap (mk' (H.subgroupOf (normalizer H))) (Subgroup.zpowers x))) = p ^ (n + 1)
    suffices Nat.card (Subtype.val ''
      ((zpowers x).comap (mk' (H.subgroupOf (normalizer H))) : Set (normalizer H))) = p ^ (n + 1)
      by convert this using 2
    rw [Nat.card_image_of_injective Subtype.val_injective
        ((zpowers x).comap (mk' (H.subgroupOf (normalizer H))) : Set (normalizer (H : Set G))),
      pow_succ, ← hH, Nat.card_congr hequiv, ← hx, ← Nat.card_zpowers, ← Nat.card_prod]
    exact Nat.card_congr
      (preimageMkEquivSubgroupProdSet (H.subgroupOf (normalizer H)) (zpowers x)), by
    intro y hy
    simp only [Subgroup.coe_subtype, mk'_apply, Subgroup.mem_map, Subgroup.mem_comap]
    refine ⟨⟨y, le_normalizer hy⟩, ⟨0, ?_⟩, rfl⟩
    dsimp only
    rw [zpow_zero, eq_comm, QuotientGroup.eq_one_iff]
    simpa using hy⟩

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [Finite G] (p : ℕ) :
    ∀ {n m : ℕ} [_hp : Fact p.Prime] (_hdvd : p ^ m ∣ Nat.card G) (H : Subgroup G)
      (_hH : Nat.card H = p ^ n) (_hnm : n ≤ m), ∃ K : Subgroup G, Nat.card K = p ^ m ∧ H ≤ K := by sorry
theorem exists_subgroup_card_pow_prime [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥
    (by rw [card_bot, pow_zero]) n.zero_le
  ⟨K, hK.1⟩

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group of size at least `p ^ n`
then there is a subgroup of cardinality `p ^ n`. -/
lemma exists_subgroup_card_pow_prime_of_le_card {n p : ℕ} (hp : p.Prime) (h : IsPGroup p G)
    (hn : p ^ n ≤ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p ^ n := by sorry
lemma exists_subgroup_le_card_pow_prime_of_le_card {n p : ℕ} (hp : p.Prime) (h : IsPGroup p G)
    {H : Subgroup G} (hn : p ^ n ≤ Nat.card H) : ∃ H' ≤ H, Nat.card H' = p ^ n := by sorry
lemma exists_subgroup_le_card_le {k p : ℕ} (hp : p.Prime) (h : IsPGroup p G) {H : Subgroup G}
    (hk : k ≤ Nat.card H) (hk₀ : k ≠ 0) : ∃ H' ≤ H, Nat.card H' ≤ k ∧ k < p * Nat.card H' := by sorry
theorem pow_dvd_card_of_pow_dvd_card [Finite G] {p n : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ^ n ∣ Nat.card G) : p ^ n ∣ Nat.card P := by sorry
theorem dvd_card_of_dvd_card [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ Nat.card G) : p ∣ Nat.card P := by sorry
theorem card_coprime_index [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    (Nat.card P).Coprime P.index :=
  let ⟨_n, hn⟩ := IsPGroup.iff_card.mp P.2
  hn.symm ▸ (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm

theorem ne_bot_of_dvd_card [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ Nat.card G) : (P : Subgroup G) ≠ ⊥ := by sorry
theorem card_eq_multiplicity [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card P = p ^ Nat.factorization (Nat.card G) p := by sorry
noncomputable def unique_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : P.Normal) : Unique (Sylow p G) := by sorry
instance characteristic_of_subsingleton {p : ℕ} [Subsingleton (Sylow p G)] (P : Sylow p G) :
    P.Characteristic := by sorry
theorem normal_of_subsingleton {p : ℕ} [Subsingleton (Sylow p G)] (P : Sylow p G) :
    P.Normal :=
  Subgroup.normal_of_characteristic _

theorem characteristic_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : P.Normal) : P.Characteristic := by sorry
theorem normal_of_normalizer_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hn : (normalizer (P : Set G)).Normal) : P.Normal := by sorry
theorem normalizer_normalizer {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    normalizer (normalizer (P : Set G)) = normalizer (P : Set G) := by sorry
theorem normal_of_all_max_subgroups_normal [Finite G]
    (hnc : ∀ H : Subgroup G, IsCoatom H → H.Normal) {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : P.Normal :=
  normalizer_eq_top_iff.mp
    (by
      rcases eq_top_or_exists_le_coatom (normalizer (P : Set G))
        with (heq | ⟨K, hK, hNK⟩)
      · exact heq
      · haveI := hnc _ hK
        have hPK : P ≤ K := le_trans le_normalizer hNK
        refine (hK.1 ?_).elim
        rw [← sup_of_le_right hNK, P.normalizer_sup_eq_top' hPK])

theorem normal_of_normalizerCondition (hnc : NormalizerCondition G) {p : ℕ} [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) : P.Normal :=
  normalizer_eq_top_iff.mp <|
    normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ <| normalizer_normalizer _

/-- If all its Sylow subgroups are normal, then a finite group is isomorphic to the direct product
of these Sylow subgroups.
-/
noncomputable def directProductOfNormal [Finite G]
    (hn : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p G), P.Normal) :
    (∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G, P) ≃* G := by sorry
end Sylow
