(* Puiseux.v *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith Sorting.

Require Import A_PosArith A_ZArith A_QArith.
Require Import Misc.
Require Import SlopeMisc.
Require Import Slope_base.
Require Import QbarM.
Require Import NbarM.
Require Import Field2.
Require Import Fpolynomial.
Require Import Fsummation.
Require Import Newton.
Require Import ConvexHullMisc.
Require Import ConvexHull.
Require Import PolyConvexHull.
Require Import NotInSegment.
Require Import Power_series.
Require Import Puiseux_series.
Require Import Ps_add.
Require Import Ps_mul.
Require Import Ps_div.
Require Import PSpolynomial.
Require Import Puiseux_base.
Require Import AlgCloCharPol.
Require Import CharactPolyn.
Require Import F1Eq.
Require Import PosOrder.
Require Import F1Prop.
Require Import InK1m.
Require Import Q_field.
Require Import RootHeadTail.
Require Import RootAnyR.

Set Implicit Arguments.

Section theorems.

Variable α : Type.
Variable R : ring α.
Variable K : field R.
Variable acf : algeb_closed_field K.

Definition multiplicity_decreases f L n :=
  let c := ac_root (Φq f L) in
  let r := root_multiplicity acf c (Φq f L) in
  let fn := nth_pol n f L in
  let Ln := nth_ns n f L in
  let cn := nth_c n f L in
  let rn := root_multiplicity acf cn (Φq fn Ln) in
  lt_dec rn r.

Theorem order_root_tail_nonneg_any_r_aux : ∀ f L c f₁ L₁ m q₀ n r,
  newton_segments f = Some L
  → pol_in_K_1_m f m
  → q₀ = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (∀ i, (i <= S n)%nat → (ps_poly_nth 0 (nth_pol i f L) ≠ 0)%ps)
  → (∀ i, (i <= S n)%nat → nth_r i f L = r)
  → (0 ≤ order (root_tail (m * q₀) n f₁ L₁))%Qbar.
Proof.
Admitted.

(* todo: group order_root_tail_nonneg_any_r_aux and this theorem together *)
Theorem order_root_tail_nonneg_any_r : ∀ f L c f₁ L₁ m q₀ n r,
  newton_segments f = Some L
  → m = ps_pol_com_polydo f
  → q₀ = q_of_m m (γ L)
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → zerop_1st_n_const_coeff n f L = false
  → root_multiplicity acf c (Φq f L) = r
  → (∀ i, (r <= nth_r i f L)%nat)
  → (0 ≤ order (root_tail (m * q₀) n f₁ L₁))%Qbar.
Proof.
Admitted.

Theorem zerop_1st_n_const_coeff_false_before : ∀ f L m,
  zerop_1st_n_const_coeff m f L = false
  → ∀ i, (i <= m)%nat →
    zerop_1st_n_const_coeff i f L = false.
Proof.
Admitted.

Theorem multiplicity_not_decreasing : ∀ f L r,
  (∀ i : nat, if multiplicity_decreases f L i then False else True)
  → root_multiplicity acf (ac_root (Φq f L)) (Φq f L) = r
  → ∀ j, (r <= nth_r j f L)%nat.
Proof.
Admitted.

Theorem in_newton_segment_when_r_constant : ∀ f L f₁ L₁ c r,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → root_multiplicity acf c (Φq f L) = S r
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (ps_poly_nth 0 f ≠ 0)%ps
  → (∀ n : nat, (S r <= nth_r n f L)%nat)
  → ∀ n fn Ln,
    zerop_1st_n_const_coeff n f₁ L₁ = false
    → fn = nth_pol n f₁ L₁
    → Ln = nth_ns n f₁ L₁
    → newton_segments fn = Some Ln.
Proof.
Admitted.

Theorem upper_bound_zerop_1st_when_r_constant : ∀ f L c f₁ L₁ m q₀ r ofs,
  newton_segments f = Some L
  → c = ac_root (Φq f L)
  → f₁ = next_pol f (β L) (γ L) c
  → L₁ = option_get phony_ns (newton_segments f₁)
  → (ps_poly_nth 0 f ≠ 0)%ps
  → m = ps_pol_com_polydo f
  → q₀ = q_of_m m (γ L)
  → root_multiplicity acf c (Φq f L) = S r
  → (∀ i : nat, if multiplicity_decreases f L i then False else True)
  → (order (ps_pol_apply f₁ (root_tail (m * q₀) 0 f₁ L₁)) =
     qfin ofs)%Qbar
  → ∀ N,
    N = Z.to_nat (2 * z_pos m * z_pos q₀ * q_num ofs)
    → zerop_1st_n_const_coeff N f₁ L₁ = true.
Proof.
Admitted.

Definition f₁_root_when_r_constant f L :=
  if fld_zerop 1%K then 0%ps
  else
    let m := ps_pol_com_polydo f in
    let q₀ := q_of_m m (γ L) in
    let f₁ := next_pol f (β L) (γ L) (ac_root (Φq f L)) in
    let L₁ := option_get phony_ns (newton_segments f₁) in
    let s := root_tail (m * q₀) 0 f₁ L₁ in
    match order (ps_pol_apply f₁ s) with
    | qfin ofs =>
        let N := Z.to_nat (2 * z_pos m * z_pos q₀ * q_num ofs) in
        if zerop_1st_n_const_coeff N f₁ L₁ then
          match lowest_with_zero_1st_const_coeff acf N f₁ L₁ with
          | O => 0%ps
          | S i' => root_head 0 i' f₁ L₁
          end
        else 0%ps
    | ∞%Qbar => s
    end.

Theorem root_for_f₁_when_r_constant : ∀ f L f₁,
  newton_segments f = Some L
  → (ps_poly_nth 0 f ≠ 0)%ps
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → (∀ i, if multiplicity_decreases f L i then False else True)
  → (ps_pol_apply f₁ (f₁_root_when_r_constant f L) = 0)%ps.
Proof.
Admitted.

Theorem degree_pos_imp_L_not_empty : ∀ f,
  degree (ps_zerop K) f ≥ 1
  → (ps_poly_nth 0 f ≠ 0)%ps
  → newton_segments f ≠ None.
Proof.
Admitted.

Theorem degree_pos_imp_has_ns : ∀ f,
  degree (ps_zerop K) f ≥ 1
  → (ps_poly_nth 0 f ≠ 0)%ps
  → ∃ L, newton_segments f = Some L.
Proof.
Admitted.

Theorem f₁_has_root : ∀ f L f₁,
  newton_segments f = Some L
  → (ps_poly_nth 0 f ≠ 0)%ps
  → f₁ = next_pol f (β L) (γ L) (ac_root (Φq f L))
  → ∃ s₁, (ps_pol_apply f₁ s₁ = 0)%ps.
Proof.
Admitted.

Theorem puiseux_series_algeb_closed : ∀ (f : polynomial (puiseux_series α)),
  degree (ps_zerop K) f ≥ 1
  → ∃ s, (ps_pol_apply f s = 0)%ps.
Proof.
Admitted.

End theorems.

Check puiseux_series_algeb_closed.
Print Assumptions puiseux_series_algeb_closed.
