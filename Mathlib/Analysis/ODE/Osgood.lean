/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.CompactExit
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Osgood's criterion for global existence

We prove that if a locally Lipschitz vector field `f` satisfies the Osgood condition
`‖f x‖ ≤ ω ‖x‖` with `∫^{∞} 1/ω(r) dr = ∞`, then solutions are global.
-/

@[expose] public section

open Filter Set MeasureTheory intervalIntegral Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (f : E → E)

/--
An Osgood-style growth package for autonomous vector fields.

The Osgood condition requires `‖f x‖ ≤ ω ‖x‖` for a continuous, non-negative modulus `ω`.
Crucially, `ω` must satisfy the Osgood condition: `∫^{∞} 1/ω(r) dr = ∞`.
-/
structure HasOsgoodGrowth (f : E → E) where
  ω : ℝ → ℝ
  c : ℝ
  h_nonneg : ∀ r, 0 ≤ ω r
  h_cont : Continuous ω
  h_pos_at_large : ∀ r, c ≤ r → 0 < ω r
  bound : ∀ x : E, ‖f x‖ ≤ ω ‖x‖
  integral_diverges : ∫⁻ r in Ioi c, ENNReal.ofReal ((ω r)⁻¹) = ⊤

namespace HasOsgoodGrowth

variable {f : E → E}

/--
Osgood potential function: `V(x) = ∫_c^x (1/ω(r)) dr`.
-/
noncomputable def osgoodPotential (h : HasOsgoodGrowth f) (x : ℝ) : ℝ :=
  ∫ r in h.c..x, (h.ω r)⁻¹

omit [NormedSpace ℝ E] in
private theorem inv_modulus_continuousOn_Ici (h : HasOsgoodGrowth f) :
    ContinuousOn (fun r => (h.ω r)⁻¹) (Ici h.c) := by
  refine h.h_cont.continuousOn.inv₀ ?_
  intro x hx
  exact (h.h_pos_at_large x hx).ne'

omit [NormedSpace ℝ E] in
private theorem osgoodPotential_hasDerivAt (h : HasOsgoodGrowth f) {x : ℝ} (hx : h.c ≤ x) :
    HasDerivAt h.osgoodPotential ((h.ω x)⁻¹) x := by
  have hcontAt : ContinuousAt (fun r => (h.ω r)⁻¹) x :=
    (h.h_cont.continuousAt.inv₀ (h.h_pos_at_large x hx).ne')
  have hs : IsOpen {y : ℝ | h.ω y ≠ 0} := by
    simpa [Set.preimage, Set.compl_setOf] using
      h.h_cont.isOpen_preimage _ (isOpen_compl_iff.mpr isClosed_singleton)
  have hmeas :
      StronglyMeasurableAtFilter (fun r => (h.ω r)⁻¹) (nhds x) volume :=
    (ContinuousAt.stronglyMeasurableAtFilter (μ := volume) hs
      (fun y hy => (h.h_cont.continuousAt.inv₀ hy))) x (h.h_pos_at_large x hx).ne'
  have hInt :
      IntervalIntegrable (fun r => (h.ω r)⁻¹) volume h.c x :=
    ((inv_modulus_continuousOn_Ici (h := h)).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hx
  exact intervalIntegral.integral_hasDerivAt_right
    hInt hmeas hcontAt

omit [NormedSpace ℝ E] in
private theorem osgoodPotential_monoOn (h : HasOsgoodGrowth f) :
    MonotoneOn h.osgoodPotential (Ici h.c) := by
  intro x hx y hy hxy
  dsimp [osgoodPotential]
  have hInt :
      IntervalIntegrable (fun r => (h.ω r)⁻¹) volume h.c y :=
    ((inv_modulus_continuousOn_Ici (h := h)).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hy
  exact intervalIntegral.integral_mono_interval (μ := volume) le_rfl hx hxy
    (Eventually.of_forall (fun x => inv_nonneg.mpr (h.h_nonneg x)))
    hInt

omit [NormedSpace ℝ E] in
theorem osgoodPotential_continuousOn (h : HasOsgoodGrowth f) :
    ContinuousOn h.osgoodPotential (Ici h.c) := by
  intro x hx
  apply (h.osgoodPotential_hasDerivAt hx).continuousAt.continuousWithinAt

omit [NormedSpace ℝ E] in
theorem osgoodPotential_at_top (h : HasOsgoodGrowth f) :
    Tendsto h.osgoodPotential atTop atTop := by
  have h_mono : MonotoneOn h.osgoodPotential (Ici h.c) := osgoodPotential_monoOn (h := h)
  have h_unbounded :
      ∀ b : ℝ, ∃ x, h.c ≤ x ∧ b ≤ h.osgoodPotential x := by
    intro b
    by_contra h_not
    push_neg at h_not
    have h_bdd : BddAbove (h.osgoodPotential '' Ici h.c) := by
      refine ⟨b, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact le_of_lt (h_not x hx)
    let U : ℝ → ℝ := fun t => h.osgoodPotential (max t h.c)
    have hU_mono : Monotone U := by
      intro t s hts
      exact h_mono (le_max_right t h.c) (le_max_right s h.c) (max_le_max hts le_rfl)
    have hU_bdd : BddAbove (range U) := by
      rcases h_bdd with ⟨B, hB⟩
      refine ⟨B, ?_⟩
      rintro y ⟨t, rfl⟩
      exact hB ⟨max t h.c, le_max_right t h.c, rfl⟩
    have hU_tendsto : Tendsto U atTop (nhds (⨆ t, U t)) :=
      tendsto_atTop_ciSup hU_mono hU_bdd
    have hV_tendsto : Tendsto h.osgoodPotential atTop (nhds (⨆ t, U t)) := by
      refine Tendsto.congr' ?_ hU_tendsto
      exact (eventually_ge_atTop h.c).mono (fun t ht => by simp [U, max_eq_left ht])
    have h_integrable :
        IntegrableOn (fun x => (h.ω x)⁻¹) (Ioi h.c) := by
      refine integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ hV_tendsto
      · intro x hx
        exact osgoodPotential_hasDerivAt (h := h) hx
      · intro x hx
        exact inv_nonneg.mpr (h.h_nonneg x)
    have h_lt_top :
        (∫⁻ x in Ioi h.c, ENNReal.ofReal ((h.ω x)⁻¹)) < ⊤ :=
      h_integrable.setLIntegral_lt_top
    exact (h_lt_top.ne h.integral_diverges).elim
  rw [tendsto_atTop_atTop]
  intro b
  rcases h_unbounded b with ⟨x, hx, hbx⟩
  refine ⟨max x h.c, ?_⟩
  intro y hy
  have hyc : h.c ≤ y := le_trans (le_max_right _ _) hy
  have hxy : x ≤ y := le_trans (le_max_left _ _) hy
  exact hbx.trans (h_mono hx hyc hxy)

private theorem slope_diff_factor {g f : ℝ → ℝ} {x y z d : ℝ} (hfx : f x = y) :
    slope (g ∘ f) x z - d * slope f x z = (slope g y (f z) - d) * slope f x z := by
  rw [slope_comp_eq hfx]
  ring

private theorem tendsto_slope_diff_zero {g f : ℝ → ℝ} {x y d : ℝ}
    (hg : HasDerivAt g d y)
    (hf : Filter.Tendsto f (nhdsWithin x (Set.Ioi x)) (nhds y))
    (hfx : f x = y)
    (hbdd : ∃ M, ∀ᶠ z in nhdsWithin x (Set.Ioi x), |slope f x z| ≤ M) :
    Tendsto (fun z => slope (g ∘ f) x z - d * slope f x z) (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
  have h_factor :
      Filter.Tendsto (fun z => (slope g y (f z) - d) * slope f x z)
        (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
    have h_cont_f : Filter.Tendsto f (nhdsWithin x (Set.Ioi x)) (nhds y) := hf
    have h_deriv_g :
        Filter.Tendsto (fun z => (g z - g y) / (z - y)) (nhdsWithin y {y}ᶜ) (nhds d) := by
      rw [hasDerivAt_iff_tendsto_slope] at hg
      simpa [div_eq_inv_mul] using hg
    have h_slope_g :
        Filter.Tendsto (fun z => (g (f z) - g y) / (f z - y))
          (nhdsWithin x (Set.Ioi x ∩ {z | f z ≠ y})) (nhds d) := by
      refine h_deriv_g.comp ?_
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_cont_f.mono_left <| nhdsWithin_mono _ <| Set.inter_subset_left,
        Filter.eventually_of_mem self_mem_nhdsWithin fun z hz => hz.2⟩
    have h_slope_g_zero :
        Filter.Tendsto (fun z => (g (f z) - g y) / (f z - y) - d)
          (nhdsWithin x (Set.Ioi x ∩ {z | f z ≠ y})) (nhds 0) := by
      simpa using h_slope_g.sub_const d
    have h_slope_g_zero_mul :
        Filter.Tendsto
          (fun z => ((g (f z) - g y) / (f z - y) - d) * ((f z - y) / (z - x)))
          (nhdsWithin x (Set.Ioi x ∩ {z | f z ≠ y})) (nhds 0) := by
      have h_slope_f_bounded :
          ∃ M, ∀ᶠ z in nhdsWithin x (Set.Ioi x), |(f z - y) / (z - x)| ≤ M := by
        simpa [slope_def_field, hfx] using hbdd
      rw [Metric.tendsto_nhds] at *
      intro ε hε
      rcases h_slope_f_bounded with ⟨M, hM⟩
      filter_upwards [h_slope_g_zero (ε / (max M 1 + 1)) (by positivity),
        hM.filter_mono <| nhdsWithin_mono _ <| Set.inter_subset_left] with z hz₁ hz₂
      simp only [dist_zero_right, norm_mul, Real.norm_eq_abs, norm_div] at *
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (by simpa [abs_div] using hz₂) (abs_nonneg _))
        (by
          rw [lt_div_iff₀] at hz₁
          · nlinarith [le_max_left M 1, le_max_right M 1,
              abs_nonneg ((g (f z) - g y) / (f z - y) - d)]
          · positivity)
    rw [Metric.tendsto_nhdsWithin_nhds] at h_slope_g_zero_mul ⊢
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := h_slope_g_zero_mul ε hε
    refine ⟨δ, hδ, ?_⟩
    intro z hz₁ hz₂
    by_cases h : f z = y
    · simp only [h, slope_same, zero_sub, slope_def_field, hfx, sub_self, zero_div, mul_zero,
        dist_self]
      exact hε
    · simp [slope_def_field, hfx]
      simpa [dist_eq_norm, abs_mul, abs_div] using H ⟨hz₁, h⟩ hz₂
  convert h_factor using 1
  exact funext fun z => by
    rw [slope_comp_eq hfx]
    ring

private theorem tendsto_slope_g_diff_d_zero {g f : ℝ → ℝ} {x y d : ℝ}
    (hg : HasDerivAt g d y) (hf : ContinuousAt f x) (hfx : f x = y) :
    Tendsto (fun z => if f z = y then 0 else slope g y (f z) - d)
      (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
  have h_eps_delta : ∀ ε > 0, ∃ δ > 0, ∀ u, |u - y| < δ ∧ u ≠ y → |slope g y u - d| < ε := by
    rw [hasDerivAt_iff_tendsto_slope] at hg
    exact fun ε ε_pos => by
      have := Metric.tendsto_nhdsWithin_nhds.mp hg ε ε_pos
      aesop
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rcases h_eps_delta ε hε with ⟨δ, hδ, H⟩
  rcases Metric.continuousAt_iff.mp hf δ hδ with ⟨δ', hδ', H'⟩
  use δ'
  aesop

private theorem slope_diff_eq_if_mul {g f : ℝ → ℝ} {x y z d : ℝ} (hfx : f x = y) :
    slope (g ∘ f) x z - d * slope f x z =
      (if f z = y then 0 else slope g y (f z) - d) * slope f x z := by
  by_cases h : f z = y
  · simp [h, slope_def_field, hfx]
  · simp [h, slope_diff_factor hfx]

private theorem tendsto_slope_diff_zero' {g f : ℝ → ℝ} {x y d : ℝ}
    (hg : HasDerivAt g d y)
    (hf : Filter.Tendsto f (nhdsWithin x (Set.Ioi x)) (nhds y))
    (hfx : f x = y)
    (hbdd : ∃ M, ∀ᶠ z in nhdsWithin x (Set.Ioi x), |slope f x z| ≤ M) :
    Tendsto (fun z => slope (g ∘ f) x z - d * slope f x z) (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
  convert tendsto_slope_diff_zero hg hf hfx hbdd using 1

private theorem liminf_slope_comp_le' {g f : ℝ → ℝ} {x y d : ℝ}
    (hg : HasDerivAt g d y) (hg' : 0 ≤ d)
    (hf : Filter.Tendsto f (nhdsWithin x (Set.Ioi x)) (nhds y))
    (hfx : f x = y)
    (hbdd : ∃ M, ∀ᶠ z in nhdsWithin x (Set.Ioi x), |slope f x z| ≤ M) :
    (liminf (fun z => slope (g ∘ f) x z) (nhdsWithin x (Set.Ioi x))) ≤
      d * (liminf (fun z => slope f x z) (nhdsWithin x (Set.Ioi x))) := by
  let F : Filter ℝ := nhdsWithin x (Set.Ioi x)
  let u : ℝ → ℝ := fun z => slope (g ∘ f) x z - d * slope f x z
  let v : ℝ → ℝ := fun z => d * slope f x z
  have hu_tendsto : Tendsto u F (nhds 0) := by
    simpa [u, F] using (tendsto_slope_diff_zero (hg := hg) (hf := hf) (hfx := hfx) hbdd)
  have hu_bdd_ge : IsBoundedUnder (· ≥ ·) F u := hu_tendsto.isBoundedUnder_ge
  have hu_bdd_le : IsBoundedUnder (· ≤ ·) F u := hu_tendsto.isBoundedUnder_le
  rcases hbdd with ⟨M, hM⟩
  have hv_bdd_ge : IsBoundedUnder (· ≥ ·) F v := by
    refine isBoundedUnder_of_eventually_ge (a := -(d * M)) ?_
    filter_upwards [hM] with z hz
    have hz_low : -M ≤ slope f x z := (abs_le.mp hz).1
    have hmul : d * (-M) ≤ d * slope f x z := mul_le_mul_of_nonneg_left hz_low hg'
    simpa [v, neg_mul] using hmul
  have hv_bdd_le : IsBoundedUnder (· ≤ ·) F v := by
    refine isBoundedUnder_of_eventually_le (a := d * M) ?_
    filter_upwards [hM] with z hz
    have hz_up : slope f x z ≤ M := (abs_le.mp hz).2
    simpa [v] using (mul_le_mul_of_nonneg_left hz_up hg')
  have hv_cobdd_ge : IsCoboundedUnder (· ≥ ·) F v := hv_bdd_le.isCoboundedUnder_ge
  have h_add : liminf (u + v) F ≤ limsup u F + liminf v F :=
    liminf_add_le hu_bdd_ge hu_bdd_le hv_bdd_ge hv_cobdd_ge
  have h_add' : liminf (fun z => u z + v z) F ≤ limsup u F + liminf v F := by
    simpa [Pi.add_apply] using h_add
  have hu_limsup : limsup u F = 0 := hu_tendsto.limsup_eq
  have h_uv : (fun z => slope (g ∘ f) x z) = (fun z => u z + v z) := by
    funext z
    dsimp [u, v]
    ring
  have h_comp_le_mul : liminf (fun z => slope (g ∘ f) x z) F ≤ liminf v F := by
    calc
      liminf (fun z => slope (g ∘ f) x z) F = liminf (fun z => u z + v z) F := by simp [h_uv]
      _ ≤ limsup u F + liminf v F := h_add'
      _ = liminf v F := by simp [hu_limsup]
  have h_comp_le_mul' :
      liminf (fun z => slope (g ∘ f) x z) (nhdsWithin x (Set.Ioi x)) ≤
        liminf (fun z => d * slope f x z) (nhdsWithin x (Set.Ioi x)) := by
    simpa [F, v] using h_comp_le_mul
  have h_slope_bdd_ge : IsBoundedUnder (· ≥ ·) F (fun z => slope f x z) := by
    refine isBoundedUnder_of_eventually_ge (a := -M) ?_
    filter_upwards [hM] with z hz
    exact (abs_le.mp hz).1
  have h_slope_bdd_le : IsBoundedUnder (· ≤ ·) F (fun z => slope f x z) := by
    refine isBoundedUnder_of_eventually_le (a := M) ?_
    filter_upwards [hM] with z hz
    exact (abs_le.mp hz).2
  have h_slope_cobdd_ge : IsCoboundedUnder (· ≥ ·) F (fun z => slope f x z) :=
    h_slope_bdd_le.isCoboundedUnder_ge
  have h_mul_map : d * liminf (fun z => slope f x z) F =
      liminf (fun z => d * slope f x z) F := by
    refine Monotone.map_liminf_of_continuousAt
      (F := F) (f := fun t : ℝ => d * t) (a := fun z => slope f x z)
      (f_incr := fun a b hab => mul_le_mul_of_nonneg_left hab hg')
      (f_cont := (continuous_const.mul continuous_id).continuousAt)
      (cobdd := h_slope_cobdd_ge) (bdd_below := h_slope_bdd_ge)
  have h_mul :
      liminf (fun z => d * slope f x z) (nhdsWithin x (Set.Ioi x)) =
        d * liminf (fun z => slope f x z) (nhdsWithin x (Set.Ioi x)) := by
    simpa [F] using h_mul_map.symm
  exact h_comp_le_mul'.trans_eq h_mul

private theorem liminf_slope_norm_le {φ : ℝ → E} {t : ℝ} {v : E}
    (hφ : Tendsto (fun z => slope φ t z) (nhdsWithin t (Set.Ioi t)) (nhds v)) :
    liminf (fun z => slope (fun s => ‖φ s‖) t z) (nhdsWithin t (Set.Ioi t)) ≤ ‖v‖ := by
  have h_deriv :
      Filter.Tendsto (fun z => ‖φ z - φ t‖ / (z - t)) (nhdsWithin t (Set.Ioi t)) (nhds ‖v‖) := by
    have := hφ
    have := this.norm
    rw [Metric.tendsto_nhdsWithin_nhds] at *
    intro ε hε
    rcases this ε hε with ⟨δ, hδ, H⟩
    exact ⟨δ, hδ, fun {x} hx₁ hx₂ => by
      have hpos : 0 < x - t := by simpa using hx₁
      have h_eq : ‖slope φ t x‖ = ‖φ x - φ t‖ / (x - t) := by
        simp only [slope, norm_smul, Real.norm_eq_abs, abs_inv, ← div_eq_inv_mul,
          abs_of_pos hpos, vsub_eq_sub]
      have : dist (‖φ x - φ t‖ / (x - t)) ‖v‖ = dist ‖slope φ t x‖ ‖v‖ := by simp [h_eq.symm]
      let H' := H hx₁ hx₂
      rw [this.symm] at H'
      exact H'
      ⟩
  have h_slope_le :
      ∀ᶠ z in nhdsWithin t (Set.Ioi t), slope (fun s => ‖φ s‖) t z ≤ ‖φ z - φ t‖ / (z - t) := by
    filter_upwards [self_mem_nhdsWithin] with z hz using by
      rw [slope_def_field]
      simpa [abs_of_nonneg (sub_nonneg.mpr hz.out.le)] using
        div_le_div_of_nonneg_right (norm_sub_norm_le (φ z) (φ t)) (sub_nonneg.mpr hz.out.le)
  by_cases h : {a : ℝ | ∀ᶠ n in nhdsWithin t (Set.Ioi t), a ≤ slope (fun s => ‖φ s‖) t n}.Nonempty
  · refine csSup_le h ?_
    intro b hb
    obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ᶠ z in nhdsWithin t (Set.Ioi t), b ≤ slope (fun s => ‖φ s‖) t z := by
      exact ⟨1, zero_lt_one, hb⟩
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_deriv
      (by
        filter_upwards [hε.2, h_slope_le] with z hz₁ hz₂
        exact le_trans hz₁ hz₂)
  · have hset : {a : ℝ | ∀ᶠ n in nhdsWithin t (Set.Ioi t), a ≤ slope (fun s => ‖φ s‖) t n} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    simp [Filter.liminf_eq, hset, norm_nonneg]

private theorem eventually_abs_slope_norm_le {φ : ℝ → E} {t : ℝ} :
    ∀ᶠ z in nhdsWithin t (Set.Ioi t), |slope (fun s => ‖φ s‖) t z| ≤ ‖slope φ t z‖ := by
  simp only [slope]
  filter_upwards [self_mem_nhdsWithin] with z hz using by
    simpa [norm_smul, abs_mul, abs_inv] using
      mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le (φ z) (φ t)) (by positivity)

private theorem exists_eventually_abs_slope_norm_le_of_tendsto_slope
    {φ : ℝ → E} {t : ℝ} {v : E}
    (h_slope : Tendsto (fun z => slope φ t z) (nhdsWithin t (Set.Ioi t)) (nhds v)) :
    ∃ M, ∀ᶠ z in nhdsWithin t (Set.Ioi t), |slope (fun s => ‖φ s‖) t z| ≤ M := by
  have h_slope_norm : Tendsto (fun z => ‖slope φ t z‖) (nhdsWithin t (Set.Ioi t)) (nhds ‖v‖) :=
    h_slope.norm
  refine ⟨‖v‖ + 1, ?_⟩
  filter_upwards [eventually_abs_slope_norm_le (φ := φ) (t := t),
    h_slope_norm.eventually (ge_mem_nhds (show ‖v‖ < ‖v‖ + 1 by linarith))] with z hz₁ hz₂
  exact le_trans hz₁ hz₂

private theorem osgood_potential_derivative_bound {f : E → E} {φ : ℝ → E} {t : ℝ}
    (h_growth : HasOsgoodGrowth f)
    (h_slope : Tendsto (fun z => slope φ t z) (nhdsWithin t (Set.Ioi t)) (nhds (f (φ t))))
    (h_cont : Tendsto φ (nhdsWithin t (Set.Ioi t)) (nhds (φ t)))
    (h_large : h_growth.c ≤ ‖φ t‖) :
    liminf (fun z => slope (h_growth.osgoodPotential ∘ (fun s => ‖φ s‖)) t z)
      (nhdsWithin t (Set.Ioi t)) ≤ 1 := by
  have h_slope_phi :
      Filter.Tendsto (fun z => slope φ t z) (nhdsWithin t (Set.Ioi t)) (nhds (f (φ t))) := h_slope
  have h_slope_norm_bdd :
      ∃ M, ∀ᶠ z in nhdsWithin t (Set.Ioi t), |slope (fun s => ‖φ s‖) t z| ≤ M :=
    exists_eventually_abs_slope_norm_le_of_tendsto_slope h_slope_phi
  have h_liminf_comp :
      liminf (fun z => slope (h_growth.osgoodPotential ∘ (fun s => ‖φ s‖)) t z)
          (nhdsWithin t (Set.Ioi t)) ≤
        (h_growth.ω (‖φ t‖))⁻¹ *
          liminf (fun z => slope (fun s => ‖φ s‖) t z) (nhdsWithin t (Set.Ioi t)) := by
    exact liminf_slope_comp_le'
      (hg := h_growth.osgoodPotential_hasDerivAt h_large)
      (hg' := inv_nonneg.2 (h_growth.h_nonneg _))
      (hf := h_cont.norm)
      (hfx := rfl)
      h_slope_norm_bdd
  have h_liminf_norm :
      liminf (fun z => slope (fun s => ‖φ s‖) t z) (nhdsWithin t (Set.Ioi t)) ≤ ‖f (φ t)‖ :=
    liminf_slope_norm_le h_slope_phi
  have hωpos : 0 < h_growth.ω (‖φ t‖) := h_growth.h_pos_at_large _ h_large
  have hωinv_nonneg : 0 ≤ (h_growth.ω (‖φ t‖))⁻¹ := inv_nonneg.mpr (le_of_lt hωpos)
  have h_mul_bound :
      (h_growth.ω (‖φ t‖))⁻¹ * ‖f (φ t)‖ ≤ 1 := by
    have hmul :
        (h_growth.ω (‖φ t‖))⁻¹ * ‖f (φ t)‖ ≤
          (h_growth.ω (‖φ t‖))⁻¹ * h_growth.ω (‖φ t‖) :=
      mul_le_mul_of_nonneg_left (h_growth.bound (φ t)) hωinv_nonneg
    have hone : (h_growth.ω (‖φ t‖))⁻¹ * h_growth.ω (‖φ t‖) = 1 := by
      field_simp [hωpos.ne']
    exact hmul.trans_eq hone
  exact h_liminf_comp.trans <|
    (mul_le_mul_of_nonneg_left h_liminf_norm hωinv_nonneg).trans h_mul_bound

private theorem tendsto_norm_right_of_maximal_univ
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h_max : IsMaximalODESolutionWithin
      (U := (Set.univ : Set (ℝ × E)))
      (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f p.1.2) φ I)
    (h_above : BddAbove I) (hf : LocallyLipschitz f) :
    Tendsto (fun t => ‖φ t‖) (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) atTop := by
  exact IsMaximalODESolutionWithin.tendsto_norm_right_time_dependent
    (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f p.1.2)
    h_max h_above
    (by
       intro K' hK'
       rcases uniform_time_of_existence_autonomous_compact_locallyLipschitz hf hK' with
         ⟨ε, hε, h_ex⟩
       refine ⟨ε, hε, ?_⟩
       filter_upwards [Filter.univ_mem] with t₀ _ _ x hx
       rcases h_ex x hx t₀ with ⟨α, hα0, hα⟩
       refine ⟨α, hα0, ?_⟩
       intro t ht
       simpa [extendVectorField] using hα t ht)
    (by
      intro p
      rcases hf p.2 with ⟨K, t, ht_mem, hLip⟩
      refine ⟨K, (Prod.snd ⁻¹' t), ContinuousAt.preimage_mem_nhds (continuousAt_snd) ht_mem, ?_⟩
      rw [lipschitzOnWith_iff_norm_sub_le] at *
      intro x hx y hy
      convert (hLip hx hy).trans (mul_le_mul_of_nonneg_left (norm_snd_le (x - y)) K.2) using 1
      simp [extendVectorField])

omit [NormedSpace ℝ E] in
private theorem exists_time_and_norm_large_near_sSup
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h_growth : HasOsgoodGrowth f) (h_above : BddAbove I) (hI_nonempty : I.Nonempty)
    (h_tendsto : Tendsto (fun t => ‖φ t‖)
      (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) atTop) :
    ∃ t₀ ∈ I, ∀ t ∈ I ∩ Ici t₀, t < sSup I → h_growth.c ≤ ‖φ t‖ := by
  have h_eventually_ge :
      ∀ᶠ t in nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I, h_growth.c ≤ ‖φ t‖ :=
    h_tendsto.eventually (Filter.eventually_ge_atTop _)
  rw [nhdsWithin, Filter.eventually_inf_principal, Filter.eventually_inf_principal]
    at h_eventually_ge
  rcases h_eventually_ge.exists_mem with ⟨S, hS, hS_impl⟩
  rcases (nhds_basis_Ioo_pos (sSup I)).mem_iff.mp hS with ⟨ε, hε, hε_sub⟩
  rcases (lt_csSup_iff h_above hI_nonempty).1 (sub_lt_self (sSup I) hε) with ⟨t₀, ht₀, ht₀_lb⟩
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht hlt
  have h_in_S : t ∈ S := by
    apply hε_sub
    rw [mem_Ioo]
    constructor
    · exact ht₀_lb.trans_le ht.2
    · exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (le_of_lt hε))
  exact hS_impl t h_in_S hlt ht.1

omit [NormedSpace ℝ E] in
private theorem osgoodPotential_comp_norm_slope_cobounded
    {f : E → E} {φ : ℝ → E} {t : ℝ}
    (h_growth : HasOsgoodGrowth f)
    (h_cont : Tendsto φ (nhdsWithin t (Set.Ioi t)) (nhds (φ t)))
    (h_large : h_growth.c ≤ ‖φ t‖)
    (h_slope_norm_bdd :
      ∃ M, ∀ᶠ z in nhdsWithin t (Set.Ioi t), |slope (fun s => ‖φ s‖) t z| ≤ M) :
    (nhdsWithin t (Set.Ioi t)).IsCoboundedUnder (· ≥ ·)
      (slope (h_growth.osgoodPotential ∘ (fun s => ‖φ s‖)) t) := by
  let g_norm : ℝ → ℝ := fun s => ‖φ s‖
  let d : ℝ := (h_growth.ω (‖φ t‖))⁻¹
  have h_slope_diff :
      Tendsto (fun z => slope (h_growth.osgoodPotential ∘ g_norm) t z - d * slope g_norm t z)
        (nhdsWithin t (Set.Ioi t)) (nhds 0) := by
    exact tendsto_slope_diff_zero'
      (g := h_growth.osgoodPotential) (f := g_norm)
      (hg := h_growth.osgoodPotential_hasDerivAt h_large)
      (hf := h_cont.norm) (hfx := rfl) h_slope_norm_bdd
  rcases h_slope_norm_bdd with ⟨M, hM⟩
  have h_mul_bdd : ∀ᶠ z in nhdsWithin t (Set.Ioi t), d * slope g_norm t z ≤ |d| * M := by
    filter_upwards [hM] with z hz
    calc
      d * slope g_norm t z ≤ |d * slope g_norm t z| := le_abs_self _
      _ = |d| * |slope g_norm t z| := by simp [abs_mul]
      _ ≤ |d| * M := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have h_diff_bdd : ∀ᶠ z in nhdsWithin t (Set.Ioi t),
      slope (h_growth.osgoodPotential ∘ g_norm) t z - d * slope g_norm t z ≤ 1 := by
    filter_upwards [h_slope_diff.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with z hz
    have hz' : |slope (h_growth.osgoodPotential ∘ g_norm) t z - d * slope g_norm t z| < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hz
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) hz')
  have h_slope_u_bdd :
      ∀ᶠ z in nhdsWithin t (Set.Ioi t),
        slope (h_growth.osgoodPotential ∘ g_norm) t z ≤ 1 + |d| * M := by
    filter_upwards [h_diff_bdd, h_mul_bdd] with z hz₁ hz₂
    calc
      slope (h_growth.osgoodPotential ∘ g_norm) t z =
          (slope (h_growth.osgoodPotential ∘ g_norm) t z - d * slope g_norm t z) +
            (d * slope g_norm t z) := by ring
      _ ≤ 1 + d * slope g_norm t z := by gcongr
      _ ≤ 1 + |d| * M := by gcongr
  exact isCoboundedUnder_ge_of_eventually_le (nhdsWithin t (Set.Ioi t)) h_slope_u_bdd

private theorem osgoodPotential_frequently_slope_lt
    {f : E → E} {φ : ℝ → E} {t r : ℝ}
    (h_growth : HasOsgoodGrowth f)
    (h_slope : Tendsto (fun z => slope φ t z) (nhdsWithin t (Set.Ioi t)) (nhds (f (φ t))))
    (h_cont : Tendsto φ (nhdsWithin t (Set.Ioi t)) (nhds (φ t)))
    (h_large : h_growth.c ≤ ‖φ t‖) (hr : 1 < r) :
    ∃ᶠ z in nhdsWithin t (Set.Ioi t),
      slope (h_growth.osgoodPotential ∘ (fun s => ‖φ s‖)) t z < r := by
  have h_liminf :
      liminf (fun z => slope (h_growth.osgoodPotential ∘ (fun s => ‖φ s‖)) t z)
        (nhdsWithin t (Set.Ioi t)) ≤ 1 :=
    osgood_potential_derivative_bound h_growth h_slope h_cont h_large
  have h_lt :
      liminf (fun z => slope (h_growth.osgoodPotential ∘ (fun s => ‖φ s‖)) t z)
        (nhdsWithin t (Set.Ioi t)) < r := lt_of_le_of_lt h_liminf hr
  have h_slope_norm_bdd :
      ∃ M, ∀ᶠ z in nhdsWithin t (Set.Ioi t), |slope (fun s => ‖φ s‖) t z| ≤ M :=
    exists_eventually_abs_slope_norm_le_of_tendsto_slope h_slope
  have h_cobdd : (nhdsWithin t (Set.Ioi t)).IsCoboundedUnder (· ≥ ·)
      (slope (h_growth.osgoodPotential ∘ (fun s => ‖φ s‖)) t) :=
    osgoodPotential_comp_norm_slope_cobounded h_growth h_cont h_large h_slope_norm_bdd
  exact frequently_lt_of_liminf_lt h_cobdd h_lt

private theorem osgoodPotential_comp_norm_le_affine_on_interval
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h_max_ODE : IsMaximalODESolution (fun _ => f) φ I)
    (h_growth : HasOsgoodGrowth f) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (h_norm_large : ∀ t ∈ I ∩ Ici t₀, t < sSup I → h_growth.c ≤ ‖φ t‖) :
    ∀ t ∈ I ∩ Ici t₀ ∩ Iio (sSup I),
      (h_growth.osgoodPotential ∘ norm ∘ φ) t ≤
        (h_growth.osgoodPotential ∘ norm ∘ φ) t₀ + (t - t₀) := by
  let u : ℝ → ℝ := h_growth.osgoodPotential ∘ norm ∘ φ
  intro t ht
  change u t ≤ u t₀ + (t - t₀)
  rw [mem_inter_iff, mem_inter_iff, mem_Ici, mem_Iio] at ht
  rcases ht with ⟨⟨htI, ht_ge⟩, ht_lt⟩
  have h_ord : OrdConnected I := h_max_ODE.isConnected_domain.isPreconnected.ordConnected
  have h_Icc_subset : Icc t₀ t ⊆ I ∩ Ici t₀ := subset_inter (h_ord.out ht₀ htI) Icc_subset_Ici_self
  apply image_le_of_liminf_slope_right_le_deriv_boundary (f := u) (a := t₀)
    (B := fun s => u t₀ + (s - t₀)) (B' := fun _ => 1)
  · have h_cont : ContinuousOn φ (Icc t₀ t) :=
      h_max_ODE.isIntegralCurveOn.continuousOn.mono (h_Icc_subset.trans inter_subset_left)
    have h_cont_norm : ContinuousOn (fun x => ‖φ x‖) (Icc t₀ t) :=
      continuous_norm.comp_continuousOn h_cont
    have h_maps : MapsTo (fun x => ‖φ x‖) (Icc t₀ t) (Ici h_growth.c) := by
      intro x hx
      have hx_in : x ∈ I ∩ Ici t₀ := h_Icc_subset hx
      have h_x_lt : x < sSup I := lt_of_le_of_lt hx.2 ht_lt
      exact h_norm_large x hx_in h_x_lt
    exact h_growth.osgoodPotential_continuousOn.comp h_cont_norm h_maps
  · simp only [sub_self, add_zero, le_refl]
  · exact continuousOn_const.add (continuousOn_id.sub continuousOn_const)
  · intro x _
    exact ((hasDerivAt_id x).sub_const t₀).const_add (u t₀) |>.hasDerivWithinAt
  · intro x hx r hr
    have h_x_lt : x < sSup I := lt_of_le_of_lt hx.2.le ht_lt
    have h_x_I : x ∈ I := (h_Icc_subset (Ico_subset_Icc_self hx)).1
    have h_deriv_within : HasDerivWithinAt φ (f (φ x)) I x := h_max_ODE.isIntegralCurveOn x h_x_I
    have h_deriv_at := h_deriv_within.hasDerivAt (h_max_ODE.isOpen_domain.mem_nhds h_x_I)
    have h_slope_phi := (hasDerivAt_iff_tendsto_slope_left_right.1 h_deriv_at).2
    have h_cont_phi : Tendsto φ (nhdsWithin x (Set.Ioi x)) (nhds (φ x)) :=
      tendsto_nhdsWithin_of_tendsto_nhds h_deriv_at.continuousAt
    have hx_in : x ∈ I ∩ Ici t₀ := h_Icc_subset (Ico_subset_Icc_self hx)
    have h_large' : h_growth.c ≤ ‖φ x‖ := h_norm_large x hx_in h_x_lt
    simpa [u, Function.comp] using
      (osgoodPotential_frequently_slope_lt h_growth h_slope_phi h_cont_phi h_large' hr)
  · exact (right_mem_Icc.2 ht_ge)

private theorem not_tendsto_atTop_of_eventually_le_affine_near_sSup
    {u : ℝ → ℝ} {I : Set ℝ} (h_above : BddAbove I) (hI_nonempty : I.Nonempty)
    {t₀ : ℝ} (h_lt_sup : ∀ t ∈ I, t < sSup I)
    (h_eventually : ∀ᶠ t in (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I),
      u t ≤ u t₀ + (t - t₀)) :
    ¬ Tendsto u (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) atTop := by
  intro h_top
  have h_bound_tendsto : Tendsto (fun t => u t₀ + (t - t₀))
      (nhdsWithin (sSup I) (Set.Iio (sSup I))) (nhds (u t₀ + (sSup I - t₀))) :=
    tendsto_const_nhds.add
      (Filter.Tendsto.sub_const (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) t₀)
  have h_lim_bound : Tendsto (fun t => u t₀ + (t - t₀))
      (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I)
      (nhds (u t₀ + (sSup I - t₀))) :=
    h_bound_tendsto.mono_left inf_le_left
  have h_top_bound : Tendsto (fun t => u t₀ + (t - t₀))
      (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) atTop :=
    Filter.tendsto_atTop_mono' _ h_eventually h_top
  have h_nonempty_inter : (Set.Iio (sSup I) ∩ I).Nonempty := by
    rcases hI_nonempty with ⟨t, htI⟩
    exact ⟨t, h_lt_sup t htI, htI⟩
  have h_eq : Set.Iio (sSup I) ∩ I = I := by
    ext t
    constructor
    · intro ht
      exact ht.2
    · intro ht
      exact ⟨h_lt_sup t ht, ht⟩
  have h_lub_inter : IsLUB (Set.Iio (sSup I) ∩ I) (sSup I) := by
    simpa [h_eq] using (isLUB_csSup hI_nonempty h_above)
  have h_neBot_inter : NeBot (nhdsWithin (sSup I) (Set.Iio (sSup I) ∩ I)) :=
    h_lub_inter.nhdsWithin_neBot h_nonempty_inter
  have h_neBot : NeBot (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) := by
    simpa [nhdsWithin_inter'] using h_neBot_inter
  haveI : NeBot (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) := h_neBot
  exact (not_tendsto_atTop_of_tendsto_nhds h_lim_bound) h_top_bound

private theorem not_bddAbove_of_osgood_growth_within_univ
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h_max : IsMaximalODESolutionWithin
      (U := (Set.univ : Set (ℝ × E)))
      (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f p.1.2) φ I)
    (hI_nonempty : I.Nonempty) (hf : LocallyLipschitz f) (h_growth : HasOsgoodGrowth f) :
    ¬ BddAbove I := by
  have h_max_ODE : IsMaximalODESolution (fun _ => f) φ I :=
    (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f) (f := φ) (I := I)).1 h_max
  intro h_above
  have h_tendsto : Tendsto (fun t => ‖φ t‖)
      (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) atTop :=
    tendsto_norm_right_of_maximal_univ (h_max := h_max) h_above hf
  obtain ⟨t₀, ht₀, h_norm_large⟩ :=
    exists_time_and_norm_large_near_sSup (h_growth := h_growth) h_above hI_nonempty h_tendsto
  have h_lt_sup : ∀ t ∈ I, t < sSup I := by
    intro t htI
    exact lt_csSup_of_mem_of_isOpen h_max_ODE.isOpen_domain h_above htI
  have ht₀_lt_sup : t₀ < sSup I := h_lt_sup t₀ ht₀
  let u : ℝ → ℝ := h_growth.osgoodPotential ∘ norm ∘ φ
  have h_u_le : ∀ t ∈ I ∩ Ici t₀ ∩ Iio (sSup I), u t ≤ u t₀ + (t - t₀) := by
    simpa [u, Function.comp] using
      osgoodPotential_comp_norm_le_affine_on_interval (h_max_ODE := h_max_ODE)
        (h_growth := h_growth) (ht₀ := ht₀) h_norm_large
  have h_eventually : ∀ᶠ t in (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I),
      u t ≤ u t₀ + (t - t₀) := by
    rw [Filter.eventually_inf_principal]
    have h_mem : Set.Ioo t₀ (sSup I) ∈ nhdsWithin (sSup I) (Set.Iio (sSup I)) := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Ioi t₀, isOpen_Ioi, ht₀_lt_sup, ?_⟩
      intro x hx
      exact ⟨hx.1, hx.2⟩
    filter_upwards [h_mem] with t ht htI
    have ht_mem : t ∈ I ∩ Set.Ici t₀ ∩ Set.Iio (sSup I) := by
      simp only [mem_inter_iff, mem_Ici, mem_Iio]
      exact ⟨⟨htI, le_of_lt ht.1⟩, ht.2⟩
    exact h_u_le t ht_mem
  have h_u_tendsto : Tendsto u
      (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) atTop := by
    simpa [u, Function.comp] using h_growth.osgoodPotential_at_top.comp h_tendsto
  have h_not_top : ¬ Tendsto u
      (nhdsWithin (sSup I) (Set.Iio (sSup I)) ⊓ principal I) atTop :=
    not_tendsto_atTop_of_eventually_le_affine_near_sSup (h_above := h_above)
      (hI_nonempty := hI_nonempty) (h_lt_sup := h_lt_sup) h_eventually
  exact h_not_top h_u_tendsto

theorem global_existence_of_osgood_growth
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h_max : IsMaximalODESolutionWithin
      (U := (Set.univ : Set (ℝ × E)))
      (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f p.1.2) φ I)
    (hI_nonempty : I.Nonempty) (hf : LocallyLipschitz f) (h_growth : HasOsgoodGrowth f) :
    ¬ BddAbove I ∧ ¬ BddBelow I := by
  have h_max_ODE : IsMaximalODESolution (fun _ => f) φ I :=
    (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f) (f := φ) (I := I)).1 h_max
  refine ⟨
    not_bddAbove_of_osgood_growth_within_univ (h_max := h_max) (hI_nonempty := hI_nonempty)
      (hf := hf) (h_growth := h_growth),
    ?_
  ⟩
  · intro h_below
    let f_rev : E → E := fun x => -f x
    let φ_rev : ℝ → E := φ ∘ Neg.neg
    let I_rev : Set ℝ := Neg.neg ⁻¹' I
    have h_rev : IsMaximalODESolution (fun _ => f_rev) φ_rev I_rev := by
      simpa [f_rev, φ_rev, I_rev] using
        (IsMaximalODESolution.comp_neg_iff (v := fun _ => f) (f := φ) (I := I)).mpr h_max_ODE
    have hI_rev_nonempty : I_rev.Nonempty := by
      rcases hI_nonempty with ⟨t, ht⟩
      exact ⟨-t, by simpa [I_rev] using ht⟩
    have hf_rev : LocallyLipschitz f_rev := by
      have h_neg : LocallyLipschitz (fun x : E => -x) :=
        (LipschitzWith.id.neg : LipschitzWith 1 (fun x : E => -x)).locallyLipschitz
      simpa [f_rev, Function.comp] using (LocallyLipschitz.comp h_neg hf)
    have h_growth_rev : HasOsgoodGrowth f_rev := by
      refine ⟨h_growth.ω, h_growth.c, h_growth.h_nonneg, h_growth.h_cont, h_growth.h_pos_at_large,
        ?_, h_growth.integral_diverges⟩
      intro x
      simpa [f_rev] using h_growth.bound x
    have hI_rev_bdd : BddAbove I_rev := BddAbove_preimage_neg h_below
    have h_max_rev : IsMaximalODESolutionWithin
        (U := (Set.univ : Set (ℝ × E)))
        (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f_rev p.1.2)
        φ_rev I_rev :=
      (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f_rev) (f := φ_rev) (I := I_rev)).2 h_rev
    exact (not_bddAbove_of_osgood_growth_within_univ (h_max := h_max_rev)
      (hI_nonempty := hI_rev_nonempty) (hf := hf_rev) (h_growth := h_growth_rev)) hI_rev_bdd

end HasOsgoodGrowth
