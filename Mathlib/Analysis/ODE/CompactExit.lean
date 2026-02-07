/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Algebra.Order.Group.Bounds
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.MaximalSolution

public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Topology.Order.Basic

/-!
# Compact-exit lemma ("lemme des bouts")

This module provides formal versions of the compact-exit lemma for maximal ODE solutions.
Roughly speaking, a maximal solution cannot remain in a fixed compact set as it approaches a
finite endpoint of its domain.

In this file, “approaches the right endpoint” and “approaches the left endpoint” are expressed
using neighborhood-within filters `𝓝[<] sSup I` and `𝓝[>] sInf I`.
The main statements are phrased in an *eventual* form along these filters, e.g.
`∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K`.

The key results are:
- `IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually`
- `IsMaximalODESolutionWithin.leavesEveryCompact_left_time_dependent_locallyLipschitz_eventually`
- `leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually_prod`
- `leavesEveryCompact_left_time_dependent_locallyLipschitz_eventually_prod`
- `IsMaximalODESolutionWithin.of_leavesEveryCompact`
- `IsMaximalODESolutionWithin.isProperExtendedCurve_time_dependent_locallyLipschitz`
- `IsMaximalODESolutionWithin.norm_unbounded_right_time_dependent_eventually`
- `IsMaximalODESolutionWithin.norm_unbounded_left_time_dependent_eventually`
- `IsMaximalODESolutionWithin.tendsto_norm_right_time_dependent`
- `IsMaximalODESolutionWithin.tendsto_norm_left_time_dependent`
- `IsMaximalODESolutionWithin.norm_unbounded_or_dist_boundary_tendsto_zero_time_dependent`
- `IsMaximalODESolutionWithin.global_existence_of_linear_growth`
- `IsMaximalODESolutionWithin.not_bddAbove_of_trapped`

For the time-dependent uniform existence input on a strip, see
`uniform_time_of_existence_time_dependent_compact_on_Icc` in `Mathlib.Analysis.ODE.PicardLindelof`.
-/

@[expose] public section

open Filter Metric Set IsMaximalODESolution
open scoped Topology Pointwise

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem eventually_right_uniform_data
    {v : ℝ → E → E} {I : Set ℝ} {K : Set E} {ε : ℝ}
    (H_eventual : ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K, ∃ α : ℝ → E,
      α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t) :
    ∃ l < sSup I, ∀ t₀, l < t₀ ∧ t₀ < sSup I → t₀ ∈ I → ∀ x ∈ K, ∃ α : ℝ → E,
      α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t := by
  have H_eventual' :
      ∀ᶠ t₀ in 𝓝[<] sSup I, t₀ ∈ I → ∀ x ∈ K, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t := by
    refine H_eventual.filter_mono ?_
    exact nhdsWithin_mono _ Iio_subset_Iic_self
  rcases (eventually_nhdsLT_iff (a := sSup I)
      (p := fun t₀ => t₀ ∈ I → ∀ x ∈ K, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t)).1
      H_eventual' with ⟨l, hl, hL⟩
  exact ⟨l, hl, fun t₀ ht => hL t₀ ht⟩

private theorem eqOn_inter_of_local_uniqueness
    {v : ℝ → E → E} {φ α : ℝ → E} {I : Set ℝ} {t ε : ℝ}
    (h : IsMaximalODESolution v φ I)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => v p.1 p.2))
    (hα : ∀ s ∈ Ioo (t - ε) (t + ε), HasDerivAt α (v s (α s)) s)
    (hαt : α t = φ t) (htI : t ∈ I) (hε : 0 < ε) :
    EqOn φ α (I ∩ Ioo (t - ε) (t + ε)) := by
  let K_int : Set ℝ := I ∩ Ioo (t - ε) (t + ε)
  have hK_open : IsOpen K_int := h.isOpen_domain.inter isOpen_Ioo
  have htK_int : t ∈ K_int := ⟨htI, by constructor <;> linarith [hε]⟩
  have hK_conn : IsConnected K_int := by
    have hI_ord : OrdConnected I := h.isConnected_domain.isPreconnected.ordConnected
    have hIoo_ord : OrdConnected (Ioo (t - ε) (t + ε)) := ordConnected_Ioo
    have hK_ord : OrdConnected K_int := OrdConnected.inter hI_ord hIoo_ord
    exact ⟨⟨t, htK_int⟩, hK_ord.isPreconnected⟩
  have hlocal : ∀ s ∈ K_int, φ s = α s → φ =ᶠ[𝓝 s] α := by
    intro s hs h_eq
    rcases h_locLip (s, φ s) with ⟨Kc, U, hU, hLipU⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hball⟩
    have hLip : ∀ᶠ t' in 𝓝 s, LipschitzOnWith Kc (fun x => v t' x) {x | (t', x) ∈ U} := by
      have ht_nhds : ∀ᶠ t' in 𝓝 s, |t' - s| < δ / 2 := by
        refine Metric.eventually_nhds_iff.mpr ⟨δ / 2, half_pos hδ, ?_⟩
        intro t' ht'
        rw [Real.dist_eq] at ht'
        exact ht'
      refine ht_nhds.mono ?_
      intro t' ht' x hx y hy
      have hx' : (t', x) ∈ U := hx
      have hy' : (t', y) ∈ U := hy
      have hLip := hLipU hx' hy'
      simp only [Prod.edist_eq, edist_self, max_eq_right (zero_le _)] at hLip
      exact hLip
    have hφ_cont : ContinuousAt φ s := by
      have hderiv := (h.isIntegralCurveOn s hs.1).hasDerivAt (h.isOpen_domain.mem_nhds hs.1)
      exact hderiv.continuousAt
    have hα_cont : ContinuousAt α s := (hα s hs.2).continuousAt
    have hφ_mem : ∀ᶠ t' in 𝓝 s, (t', φ t') ∈ U := by
      have hprod_cont : ContinuousAt (fun t' => (t', φ t')) s :=
        continuousAt_id.prodMk hφ_cont
      exact hprod_cont.preimage_mem_nhds hU
    have hα_mem : ∀ᶠ t' in 𝓝 s, (t', α t') ∈ U := by
      have hU' : U ∈ 𝓝 (s, α s) := by simpa [h_eq] using hU
      have hprod_cont : ContinuousAt (fun t' => (t', α t')) s :=
        continuousAt_id.prodMk hα_cont
      exact hprod_cont.preimage_mem_nhds hU'
    have hI_mem : ∀ᶠ t' in 𝓝 s, t' ∈ I := h.isOpen_domain.mem_nhds hs.1
    have hIoo_mem : ∀ᶠ u in 𝓝 s, u ∈ Ioo (t - ε) (t + ε) := isOpen_Ioo.mem_nhds hs.2
    have hφ_deriv : ∀ᶠ u in 𝓝 s, HasDerivAt φ (v u (φ u)) u := by
      refine hI_mem.mono ?_
      intro u huI
      exact (h.isIntegralCurveOn u huI).hasDerivAt (h.isOpen_domain.mem_nhds huI)
    have hα_deriv : ∀ᶠ u in 𝓝 s, HasDerivAt α (v u (α u)) u := by
      refine hIoo_mem.mono ?_
      intro u huIoo
      exact hα u huIoo
    have hφ_ev : ∀ᶠ u in 𝓝 s, HasDerivAt φ (v u (φ u)) u ∧ φ u ∈ {x | (u, x) ∈ U} :=
      hφ_deriv.and (hφ_mem.mono fun u hu => hu)
    have hα_ev : ∀ᶠ u in 𝓝 s, HasDerivAt α (v u (α u)) u ∧ α u ∈ {x | (u, x) ∈ U} :=
      hα_deriv.and (hα_mem.mono fun u hu => hu)
    exact ODE_solution_unique_of_eventually (v := v) (s := fun u => {x | (u, x) ∈ U})
      hLip hφ_ev hα_ev (by simp [h_eq])
  let S : Set ℝ := {s | s ∈ K_int ∧ φ s = α s}
  have hS_open : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 ?_
    intro s hs
    have hEq_ev : φ =ᶠ[𝓝 s] α := hlocal s hs.1 hs.2
    have hK_nhds : ∀ᶠ t' in 𝓝 s, t' ∈ K_int := hK_open.mem_nhds hs.1
    have hS_nhds : S ∈ 𝓝 s := by
      refine (hK_nhds.and hEq_ev).mono ?_
      rintro t' ⟨ht'K, ht'Eq⟩
      exact ⟨ht'K, ht'Eq⟩
    exact hS_nhds
  have hφ_cont_on : ContinuousOn φ K_int := h.isIntegralCurveOn.continuousOn.mono (fun _ hx => hx.1)
  have hα_cont_on : ContinuousOn α K_int := by
    intro s hs
    exact (hα s hs.2).continuousAt.continuousWithinAt
  have hS_closure : closure S ∩ K_int ⊆ S := by
    intro x hx
    rcases hx with ⟨hx_cl, hxK⟩
    let S' : Set {t' // t' ∈ K_int} := {t' | φ t' = α t'}
    have hS_eq : S = (Subtype.val) '' S' := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨hyK, hyEq⟩
        exact ⟨⟨y, hyK⟩, hyEq, rfl⟩
      · intro hy
        rcases hy with ⟨⟨y, hyK⟩, hyEq, rfl⟩
        exact ⟨hyK, hyEq⟩
    have hcontφ : Continuous (K_int.restrict φ) := hφ_cont_on.restrict
    have hcontα : Continuous (K_int.restrict α) := hα_cont_on.restrict
    have hS'closed : IsClosed S' := by simpa [S'] using isClosed_eq hcontφ hcontα
    have hx' : (⟨x, hxK⟩ : {t' // t' ∈ K_int}) ∈ closure S' := by
      have : x ∈ closure ((Subtype.val) '' S') := by simpa [hS_eq] using hx_cl
      exact (closure_subtype (x := ⟨x, hxK⟩) (s := S')).2 this
    have hxS' : (⟨x, hxK⟩ : {t' // t' ∈ K_int}) ∈ S' := hS'closed.closure_subset hx'
    exact ⟨hxK, hxS'⟩
  have hK_preconn : IsPreconnected K_int := hK_conn.isPreconnected
  have hS_nonempty : (K_int ∩ S).Nonempty := ⟨t, htK_int, htK_int, by simp [hαt]⟩
  have hsubset : K_int ⊆ S :=
    hK_preconn.subset_of_closure_inter_subset hS_open hS_nonempty hS_closure
  intro s hs
  exact (hsubset hs).2

private theorem splice_integralCurveOn_union
    {v : ℝ → E → E} {φ α : ℝ → E} {I : Set ℝ} {t ε : ℝ}
    [DecidablePred (fun s => s ∈ I)]
    (h : IsMaximalODESolution v φ I)
    (hα : ∀ s ∈ Ioo (t - ε) (t + ε), HasDerivAt α (v s (α s)) s)
    (h_eq_on : EqOn φ α (I ∩ Ioo (t - ε) (t + ε))) :
    IsIntegralCurveOn (fun s => if s ∈ I then φ s else α s) v (I ∪ Ioo (t - ε) (t + ε)) := by
  classical
  intro s hs
  by_cases hsI : s ∈ I
  · have hφ_deriv : HasDerivAt φ (v s (φ s)) s :=
      (h.isIntegralCurveOn s hsI).hasDerivAt (h.isOpen_domain.mem_nhds hsI)
    have h_eq : (fun s => if s ∈ I then φ s else α s) =ᶠ[𝓝 s] φ := by
      filter_upwards [h.isOpen_domain.mem_nhds hsI] with y hyI
      simp [hyI]
    have h' : HasDerivAt (fun s => if s ∈ I then φ s else α s)
        (v s ((fun s => if s ∈ I then φ s else α s) s)) s := by
      have h' := HasDerivAt.congr_of_eventuallyEq hφ_deriv h_eq
      simpa [hsI] using h'
    exact h'.hasDerivWithinAt
  · have hsIoo : s ∈ Ioo (t - ε) (t + ε) := hs.resolve_left hsI
    have hα_deriv : HasDerivAt α (v s (α s)) s := hα s hsIoo
    have h_eq : (fun s => if s ∈ I then φ s else α s) =ᶠ[𝓝 s] α := by
      have hIoo_nhds : Ioo (t - ε) (t + ε) ∈ 𝓝 s := isOpen_Ioo.mem_nhds hsIoo
      filter_upwards [hIoo_nhds] with y hyIoo
      by_cases hyI : y ∈ I
      · have : y ∈ I ∩ Ioo (t - ε) (t + ε) := ⟨hyI, hyIoo⟩
        have h_eq_on' := h_eq_on this
        simp [hyI, h_eq_on']
      · simp [hyI]
    have h' : HasDerivAt (fun s => if s ∈ I then φ s else α s)
        (v s ((fun s => if s ∈ I then φ s else α s) s)) s := by
      have h' := HasDerivAt.congr_of_eventuallyEq hα_deriv h_eq
      simpa [hsI] using h'
    exact h'.hasDerivWithinAt

private theorem contradiction_from_strict_extension_right
    {v : ℝ → E → E} {φ α : ℝ → E} {I : Set ℝ} {t ε : ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddAbove I) (htI : t ∈ I) (hε : 0 < ε)
    (ht_gt_eps : sSup I - ε / 2 < t)
    (hα : ∀ s ∈ Ioo (t - ε) (t + ε), HasDerivAt α (v s (α s)) s)
    (h_eq_on : EqOn φ α (I ∩ Ioo (t - ε) (t + ε))) :
    False := by
  classical
  let J : Set ℝ := I ∪ Ioo (t - ε) (t + ε)
  let g : ℝ → E := fun s => if s ∈ I then φ s else α s
  have hJ_open : IsOpen J := h.isOpen_domain.union isOpen_Ioo
  have hJ_conn : IsConnected J := by
    have h_inter_nonempty : (I ∩ Ioo (t - ε) (t + ε)).Nonempty := by
      refine ⟨t, htI, ?_⟩
      exact ⟨by nlinarith [hε], by nlinarith [hε]⟩
    exact IsConnected.union
      h_inter_nonempty h.isConnected_domain (isConnected_Ioo (by nlinarith [hε]))
  have hJ_curve : IsIntegralCurveOn g v J := by
    simpa [g, J] using splice_integralCurveOn_union (h := h) hα h_eq_on
  have hEq : EqOn φ g I := by
    intro s hsI
    simp [g, hsI]
  have hsup : ∃ t', t' ∈ J ∧ sSup I < t' := by
    refine ⟨t + ε / 2, ?_, ?_⟩
    · have : t + ε / 2 ∈ Ioo (t - ε) (t + ε) := by
        constructor <;> nlinarith [hε]
      exact Or.inr this
    · have ht_close : sSup I - ε / 2 < t := ht_gt_eps
      nlinarith [ht_close]
  rcases hsup with ⟨t', ht'J, ht'_sup⟩
  have h_eq : I = J := h.isMaximal g J hJ_curve hJ_open hJ_conn (subset_union_left) hEq
  have ht_le : t' ≤ sSup I := by
    have : t' ∈ I := by simpa [h_eq] using ht'J
    exact le_csSup hI this
  exact (not_lt_of_ge ht_le) ht'_sup

namespace IsMaximalODESolutionWithin

/--
Domain-restricted compact-exit lemma at the **right** endpoint (time-dependent, eventual form).

Let `φ` be a maximal ODE solution within `U` (in the sense of `IsMaximalODESolutionWithin`) with
domain `I`. Assume `I` is bounded above and that we have a uniform local existence hypothesis for
the (extended) vector field near `sSup I`, together with a (joint) locally Lipschitz hypothesis.
Then `φ` eventually leaves every compact set as `t → sSup I` from the left (within `I`).

The conclusion is stated as an eventual property along `𝓝[<] sSup I`:
`∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K`.
-/
theorem leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h0 : IsMaximalODESolutionWithin U v φ I) (hI : BddAbove I)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K := by
  let v : ℝ → E → E := extendVectorField U v
  let h : IsMaximalODESolution v φ I := by
    simpa [v] using h0.toIsMaximal
  classical
  rcases h_uniform K hK with ⟨ε₀, hε₀, H_eventual⟩
  rcases eventually_right_uniform_data (I := I) (K := K) (ε := ε₀) (v := v) H_eventual with
    ⟨l₀, hl₀, H₀⟩
  refine (eventually_nhdsLT_iff (a:=sSup I) (p:=fun t => t ∈ I → φ t ∉ K)).2 ?_
  refine ⟨max (sSup I - ε₀ / 2) l₀, ?_, ?_⟩
  · have h1 : sSup I - ε₀ / 2 < sSup I := sub_lt_self _ (half_pos hε₀)
    exact max_lt_iff.mpr ⟨h1, hl₀⟩
  · intro t ht htI
    have ht_gt_eps : sSup I - ε₀ / 2 < t :=
      lt_of_le_of_lt (le_max_left _ _) ht.1
    have ht_gt_l0 : l₀ < t :=
      lt_of_le_of_lt (le_max_right _ _) ht.1
    by_contra htK
    rcases H₀ t ⟨ht_gt_l0, ht.2⟩ htI (φ t) htK with ⟨α, hαt, hα⟩
    have h_eq_on : EqOn φ α (I ∩ Ioo (t - ε₀) (t + ε₀)) :=
      eqOn_inter_of_local_uniqueness (h := h) (h_locLip := h_locLip) hα hαt htI hε₀
    exact contradiction_from_strict_extension_right
      (h := h) hI htI hε₀ ht_gt_eps hα h_eq_on

private theorem uniform_data_timeReversal
    {v : ℝ → E → E} {I : Set ℝ}
    (_hI : BddBelow I) (_hI_nonempty : I.Nonempty)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≥] sInf I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t) :
    ∀ K' : Set E, IsCompact K' → ∃ ε > 0,
      ∀ᶠ t₀ in 𝓝[≤] sSup (Neg.neg ⁻¹' I), t₀ ∈ (Neg.neg ⁻¹' I) → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((fun s x ↦ -v (-s) x) t (α t)) t := by
  intro K' hK'
  rcases h_uniform K' hK' with ⟨ε₀, hε₀, H_eventual⟩
  refine ⟨ε₀, hε₀, ?_⟩
  let I_rev : Set ℝ := Neg.neg ⁻¹' I
  have h_rev_bound : sSup I_rev = -sInf I := by
    simp [I_rev]
  have h_eventual_rev :
      ∀ᶠ t₀ in 𝓝[≤] sSup I_rev, t₀ ∈ I_rev → ∀ x ∈ K', ∃ β : ℝ → E,
        β (-t₀) = x ∧ ∀ t ∈ Ioo (-t₀ - ε₀) (-t₀ + ε₀),
          HasDerivAt β (v t (β t)) t := by
    have hS :
        {t₀ | t₀ ∈ I → ∀ x ∈ K', ∃ β : ℝ → E,
          β t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε₀) (t₀ + ε₀), HasDerivAt β (v t (β t)) t} ∈
        𝓝[≥] sInf I := H_eventual
    rcases mem_nhdsWithin.mp hS with ⟨U, hU_open, hU_mem, hU_sub⟩
    let U_rev : Set ℝ := Neg.neg ⁻¹' U
    have hU_rev_open : IsOpen U_rev := hU_open.preimage continuous_neg
    have hU_rev_mem : -sInf I ∈ U_rev := by simpa [U_rev] using hU_mem
    have hU_rev_sub : U_rev ∩ Iic (-sInf I) ⊆
        {t₀ | t₀ ∈ I_rev → ∀ x ∈ K', ∃ β : ℝ → E,
          β (-t₀) = x ∧ ∀ t ∈ Ioo (-t₀ - ε₀) (-t₀ + ε₀), HasDerivAt β (v t (β t)) t} := by
      intro t ht
      rcases ht with ⟨htU, htle⟩
      have htU' : -t ∈ U := by simpa [U_rev] using htU
      have htle' : t ≤ -sInf I := by simpa using htle
      have htge : sInf I ≤ -t := by linarith [htle']
      have hP :
          (-t ∈ I → ∀ x ∈ K', ∃ β : ℝ → E,
            β (-t) = x ∧ ∀ s ∈ Ioo (-t - ε₀) (-t + ε₀), HasDerivAt β (v s (β s)) s) := by
        have hP' := hU_sub ⟨htU', htge⟩
        dsimp at hP'
        exact hP'
      intro htIrev
      have htI : -t ∈ I := by simpa [I_rev] using htIrev
      exact hP htI
    have hS_rev :
        {t₀ | t₀ ∈ I_rev → ∀ x ∈ K', ∃ β : ℝ → E,
          β (-t₀) = x ∧ ∀ t ∈ Ioo (-t₀ - ε₀) (-t₀ + ε₀), HasDerivAt β (v t (β t)) t} ∈
        𝓝[≤] sSup I_rev := by
      refine mem_nhdsWithin.mpr ?_
      refine ⟨U_rev, hU_rev_open, ?_, ?_⟩
      · have : -sInf I ∈ U_rev := hU_rev_mem
        simpa [h_rev_bound] using this
      · intro t ht
        have ht' : t ∈ U_rev ∩ Iic (-sInf I) := by simpa [h_rev_bound] using ht
        exact hU_rev_sub ht'
    exact hS_rev
  refine h_eventual_rev.mono ?_
  intro t₀ ht₀ htIrev x hx
  rcases ht₀ htIrev x hx with ⟨β, hβ0, hβ⟩
  refine ⟨β ∘ Neg.neg, by simp [hβ0], ?_⟩
  intro t ht
  have ht' : -t ∈ Ioo (-t₀ - ε₀) (-t₀ + ε₀) := by
    constructor <;> linarith [ht.1, ht.2]
  have hβ' : HasDerivAt β (v (-t) (β (-t))) (-t) := hβ (-t) ht'
  have hcomp := HasDerivAt.scomp (g₁ := β) (h := Neg.neg) (x := t)
    (g₁' := v (-t) (β (-t))) (h' := -1) hβ' (hasDerivAt_neg t)
  simpa [I_rev, Function.comp] using hcomp

omit [NormedSpace ℝ E] in
private theorem locallyLipschitz_timeReversal
    {v : ℝ → E → E}
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => v p.1 p.2)) :
    LocallyLipschitz (fun p : ℝ × E => (fun t x ↦ -v (-t) x) p.1 p.2) := by
  have h_neg_t : LocallyLipschitz (fun t : ℝ => -t) :=
    (LipschitzWith.id.neg : LipschitzWith 1 (fun t : ℝ => -t)).locallyLipschitz
  have h_fst : LocallyLipschitz (Prod.fst : ℝ × E → ℝ) :=
    (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × E → ℝ)).locallyLipschitz
  have h_snd : LocallyLipschitz (Prod.snd : ℝ × E → E) :=
    (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × E → E)).locallyLipschitz
  have h_fst_neg : LocallyLipschitz (fun p : ℝ × E => -p.1) := by
    simpa [Function.comp] using (LocallyLipschitz.comp h_neg_t h_fst)
  have h_neg_prod : LocallyLipschitz (fun p : ℝ × E => (-p.1, p.2)) := by
    simpa using (LocallyLipschitz.prodMk h_fst_neg h_snd)
  have h_v_comp : LocallyLipschitz (fun p : ℝ × E => v (-p.1) p.2) := by
    simpa [Function.comp] using (LocallyLipschitz.comp h_locLip h_neg_prod)
  have h_neg_x : LocallyLipschitz (fun x : E => -x) :=
    (LipschitzWith.id.neg : LipschitzWith 1 (fun x : E => -x)).locallyLipschitz
  simpa [Function.comp] using (LocallyLipschitz.comp h_neg_x h_v_comp)

omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
private theorem eventually_left_from_eventually_right_timeReversal
    {φ : ℝ → E} {I : Set ℝ} {K : Set E}
    (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (h_event_rev : ∀ᶠ t in 𝓝[<] sSup (Neg.neg ⁻¹' I), t ∈ (Neg.neg ⁻¹' I) → (φ ∘ Neg.neg) t ∉ K) :
    ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K := by
  have h_rev_bound : sSup (Neg.neg ⁻¹' I) = -sInf I := sSup_preimage_neg hI_nonempty hI
  rcases (eventually_nhdsLT_iff (a := sSup (Neg.neg ⁻¹' I))
      (p := fun t => t ∈ (Neg.neg ⁻¹' I) → (φ ∘ Neg.neg) t ∉ K)).1 h_event_rev with
    ⟨l, hl, hl_prop⟩
  refine (eventually_nhdsGT_iff (a := sInf I) (p := fun t => t ∈ I → φ t ∉ K)).2 ?_
  refine ⟨-l, ?_, ?_⟩
  · have : l < sSup (Neg.neg ⁻¹' I) := hl
    rw [h_rev_bound] at this
    linarith
  · intro t ht htI
    have ht' : l < -t ∧ -t < sSup (Neg.neg ⁻¹' I) := by
      have h1 : l < -t := by linarith [ht.2]
      have h2 : -t < sSup (Neg.neg ⁻¹' I) := by
        have : -t < -sInf I := by linarith [ht.1]
        simpa [h_rev_bound] using this
      exact ⟨h1, h2⟩
    have htI' : -t ∈ (Neg.neg ⁻¹' I) := by simpa using htI
    have hnot := hl_prop (-t) ht' htI'
    simpa [Function.comp] using hnot

/--
Domain-restricted compact-exit lemma at the **left** endpoint (time-dependent, eventual form).

This is the time-reversal of
`IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually`.
Under the analogous uniform local existence and locally Lipschitz hypotheses near `sInf I`, a
maximal solution eventually leaves any compact set as `t → sInf I` from the right (within `I`).

The conclusion is stated as an eventual property along `𝓝[>] sInf I`:
`∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K`.
-/
theorem leavesEveryCompact_left_time_dependent_locallyLipschitz_eventually
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h0 : IsMaximalODESolutionWithin U v φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≥] sInf I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K := by
  let v : ℝ → E → E := extendVectorField U v
  let h : IsMaximalODESolution v φ I := by
    simpa [v] using h0.toIsMaximal
  let v_rev := fun t x ↦ - v (-t) x
  let f_rev := φ ∘ Neg.neg
  let I_rev := Neg.neg ⁻¹' I
  have h_rev : IsMaximalODESolution v_rev f_rev I_rev := by
    simpa [v_rev, f_rev, I_rev] using (comp_neg_iff (v := v) (f := φ) (I := I)).mpr h
  have hI_rev_bdd : BddAbove I_rev := BddAbove_preimage_neg hI
  have h_uniform' : ∀ K' : Set E, IsCompact K' → ∃ ε > 0,
      ∀ᶠ t₀ in 𝓝[≤] sSup I_rev, t₀ ∈ I_rev → ∀ x ∈ K', ∃ α,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v_rev t (α t)) t := by
    intro K' hK'
    simpa [I_rev, v_rev] using uniform_data_timeReversal (v := v) hI hI_nonempty h_uniform K' hK'
  have h_locLip' : LocallyLipschitz (fun p : ℝ × E => v_rev p.1 p.2) := by
    simpa [v_rev] using locallyLipschitz_timeReversal (v := v) h_locLip
  let v_rev_sub :
      {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} → E := fun p => v_rev p.1.1 p.1.2
  have h_rev_within :
      IsMaximalODESolutionWithin (U := (Set.univ : Set (ℝ × E))) v_rev_sub f_rev I_rev := by
    refine ⟨?_, ?_⟩
    · have hExt :
        extendVectorField (U := (Set.univ : Set (ℝ × E))) v_rev_sub = v_rev := by
        funext t x
        simp [v_rev_sub, extendVectorField]
      simpa [hExt] using h_rev
    · intro t ht
      simp
  have h_uniform_rev :
      ∀ K' : Set E, IsCompact K' → ∃ ε > 0,
        ∀ᶠ t₀ in 𝓝[≤] sSup I_rev, t₀ ∈ I_rev → ∀ x ∈ K', ∃ α : ℝ → E,
          α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
            HasDerivAt α
              ((extendVectorField (U := (Set.univ : Set (ℝ × E))) v_rev_sub) t (α t)) t := by
    intro K' hK'
    rcases h_uniform' K' hK' with ⟨ε, hε, hEv⟩
    refine ⟨ε, hε, hEv.mono ?_⟩
    intro t₀ ht₀ htI x hx
    rcases ht₀ htI x hx with ⟨α, hα0, hα⟩
    refine ⟨α, hα0, ?_⟩
    intro t ht
    simpa [v_rev_sub, extendVectorField] using hα t ht
  have h_locLip_rev :
      LocallyLipschitz
        (fun p : ℝ × E =>
          (extendVectorField (U := (Set.univ : Set (ℝ × E))) v_rev_sub) p.1 p.2) := by
    simpa [v_rev_sub, extendVectorField] using h_locLip'
  have h_event_rev : ∀ᶠ t in 𝓝[<] sSup I_rev, t ∈ I_rev → f_rev t ∉ K :=
    IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually
      (h0 := h_rev_within) hI_rev_bdd K hK h_uniform_rev h_locLip_rev
  exact eventually_left_from_eventually_right_timeReversal (φ := φ) (I := I) (K := K)
    hI hI_nonempty (by simpa [I_rev, f_rev] using h_event_rev)

/--
Domain-restricted compact-exit lemma at the **right** endpoint (product-space version).

This is a convenience wrapper around
`IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually`
applied to the curve `t ↦ (t, φ t)`. It upgrades escape from compact sets in `E` to escape from
compact sets in `ℝ × E`.
-/
theorem
  leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually_prod
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolutionWithin U v φ I) (hI : BddAbove I)
    (K : Set (ℝ × E)) (hK : IsCompact K)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → (t, φ t) ∉ K := by
  let K' : Set E := Prod.snd '' K
  have hK' : IsCompact K' := hK.image continuous_snd
  have hEvent :=
    IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually
      (h0 := h) hI K' hK' h_uniform h_locLip
  refine hEvent.mono ?_
  intro t ht htI htK
  apply ht htI
  exact ⟨(t, φ t), htK, rfl⟩

/--
Domain-restricted compact-exit lemma at the **left** endpoint (product-space version).

This is the product-space analogue of
`IsMaximalODESolutionWithin.leavesEveryCompact_left_time_dependent_locallyLipschitz_eventually`.
It asserts that the graph `t ↦ (t, φ t)` eventually leaves any compact subset of `ℝ × E` as
`t → sInf I` from the right (within `I`).
-/
theorem
  leavesEveryCompact_left_time_dependent_locallyLipschitz_eventually_prod
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolutionWithin U v φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set (ℝ × E)) (hK : IsCompact K)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≥] sInf I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → (t, φ t) ∉ K := by
  let K' : Set E := Prod.snd '' K
  have hK' : IsCompact K' := hK.image continuous_snd
  have hEvent :=
    IsMaximalODESolutionWithin.leavesEveryCompact_left_time_dependent_locallyLipschitz_eventually
      (h0 := h) hI hI_nonempty K' hK' h_uniform h_locLip
  refine hEvent.mono ?_
  intro t ht htI htK
  apply ht htI
  exact ⟨(t, φ t), htK, rfl⟩

end IsMaximalODESolutionWithin

/--
Time-dependent finite-time norm blow-up (right endpoint; eventual form) for domain-restricted
maximal solutions.
-/
theorem IsMaximalODESolutionWithin.norm_unbounded_right_time_dependent_eventually
    [ProperSpace E]
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolutionWithin U v φ I) (hI : BddAbove I)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    ∀ R : ℝ, ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → R < ‖φ t‖ := by
  intro R
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall _ _
  have hEvent :=
    IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually
      (h0 := h) hI (closedBall (0 : E) R) hK h_uniform h_locLip
  refine hEvent.mono ?_
  intro t ht htI
  have : ¬ ‖φ t‖ ≤ R := by
    intro hle
    exact ht htI (by simpa [mem_closedBall, dist_eq_norm] using hle)
  exact lt_of_not_ge this

/--
Time-dependent finite-time norm blow-up (left endpoint; eventual form) for domain-restricted
maximal solutions.
-/
theorem IsMaximalODESolutionWithin.norm_unbounded_left_time_dependent_eventually
    [ProperSpace E]
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolutionWithin U v φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≥] sInf I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    ∀ R : ℝ, ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → R < ‖φ t‖ := by
  intro R
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall _ _
  have hEvent :=
    IsMaximalODESolutionWithin.leavesEveryCompact_left_time_dependent_locallyLipschitz_eventually
      (h0 := h) hI hI_nonempty (closedBall (0 : E) R) hK h_uniform h_locLip
  refine hEvent.mono ?_
  intro t ht htI
  have : ¬ ‖φ t‖ ≤ R := by
    intro hle
    exact ht htI (by simpa [mem_closedBall, dist_eq_norm] using hle)
  exact lt_of_not_ge this

/--
Time-dependent finite-time norm blow-up (right endpoint; tendsto form) for domain-restricted
maximal solutions.
-/
theorem IsMaximalODESolutionWithin.tendsto_norm_right_time_dependent
    [ProperSpace E]
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolutionWithin U v φ I) (hI : BddAbove I)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    Tendsto (fun t => ‖φ t‖) (𝓝[<] sSup I ⊓ 𝓟 I) atTop := by
  refine tendsto_atTop.2 ?_
  intro R
  have hEvent :=
    IsMaximalODESolutionWithin.norm_unbounded_right_time_dependent_eventually
      (h := h) hI h_uniform h_locLip R
  exact ((eventually_inf_principal).2 hEvent).mono fun _ ht => le_of_lt ht

/--
Time-dependent finite-time norm blow-up (left endpoint; tendsto form) for domain-restricted
maximal solutions.
-/
theorem IsMaximalODESolutionWithin.tendsto_norm_left_time_dependent
    [ProperSpace E]
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolutionWithin U v φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≥] sInf I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    Tendsto (fun t => ‖φ t‖) (𝓝[>] sInf I ⊓ 𝓟 I) atTop := by
  refine tendsto_atTop.2 ?_
  intro R
  have hEvent :=
    IsMaximalODESolutionWithin.norm_unbounded_left_time_dependent_eventually
      (h := h) hI hI_nonempty h_uniform h_locLip R
  exact ((eventually_inf_principal).2 hEvent).mono fun _ ht => le_of_lt ht

/--
Time-dependent escape lemma in an open domain `U ⊆ ℝ × E` (right endpoint; eventual form).
-/
theorem IsMaximalODESolutionWithin.norm_unbounded_or_dist_boundary_tendsto_zero_time_dependent
    [ProperSpace E]
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolutionWithin U v φ I) (hI : BddAbove I)
    (hU : IsOpen U)
    (h_uniform : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    ∀ R : ℝ, ∀ δ > 0, ∀ᶠ t in 𝓝[<] sSup I, t ∈ I →
      (R < ‖φ t‖ ∨ infDist (t, φ t) Uᶜ < δ) := by
  intro R δ hδ
  let K : Set (ℝ × E) := {p | p.1 ∈ Icc (sSup I - 1) (sSup I) ∧ ‖p.2‖ ≤ R ∧ δ ≤ infDist p Uᶜ}
  have hU_closed : IsClosed Uᶜ := isClosed_compl_iff.mpr hU
  have hcontInfDist : Continuous (fun p : ℝ × E => infDist p Uᶜ) := by
    have hcont' : Continuous (fun p : ℝ × E => infDist p (closure Uᶜ)) :=
      continuous_infDist_pt (s := closure Uᶜ)
    simpa [hU_closed.closure_eq] using hcont'
  have hK_closed : IsClosed K := by
    have hA : IsClosed {p : ℝ × E | p.1 ∈ Icc (sSup I - 1) (sSup I)} :=
      isClosed_Icc.preimage continuous_fst
    have hB : IsClosed {p : ℝ × E | ‖p.2‖ ≤ R} :=
      isClosed_le (continuous_norm.comp continuous_snd) continuous_const
    have hC : IsClosed {p : ℝ × E | δ ≤ infDist p Uᶜ} :=
      isClosed_le continuous_const hcontInfDist
    simpa [K] using hA.inter (hB.inter hC)
  have hK_sub :
      K ⊆ (Icc (sSup I - 1) (sSup I) ×ˢ closedBall (0 : E) R) := by
    intro p hp
    exact ⟨hp.1, by simpa [mem_closedBall, dist_eq_norm] using hp.2.1⟩
  have hK_big_compact : IsCompact (Icc (sSup I - 1) (sSup I) ×ˢ closedBall (0 : E) R) :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : E) R))
  have hK : IsCompact K := by
    exact IsCompact.of_isClosed_subset hK_big_compact hK_closed hK_sub
  open IsMaximalODESolutionWithin in
  have hExit :=
    leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually_prod
      (h := h) hI K hK h_uniform h_locLip
  have hNear : ∀ᶠ t in 𝓝[<] sSup I, sSup I - 1 < t := by
    refine (eventually_nhdsLT_iff (a := sSup I) (p := fun t => sSup I - 1 < t)).2 ?_
    refine ⟨sSup I - 1, by linarith, ?_⟩
    intro t ht
    exact ht.1
  refine (hExit.and hNear).mono ?_
  intro t ht htI
  rcases ht with ⟨hNotK, htLower⟩
  have hNotBoth : ¬ (‖φ t‖ ≤ R ∧ δ ≤ infDist (t, φ t) Uᶜ) := by
    intro hBoth
    have hNotK' : (t, φ t) ∉ K := hNotK htI
    apply hNotK'
    have htIcc : t ∈ Icc (sSup I - 1) (sSup I) := ⟨le_of_lt htLower, le_csSup hI htI⟩
    exact ⟨htIcc, hBoth.1, hBoth.2⟩
  exact (not_and_or.mp hNotBoth).elim (fun hle => Or.inl (lt_of_not_ge hle))
    (fun hle => Or.inr (lt_of_not_ge hle))

omit [NormedSpace ℝ E] in
private theorem exit_right_contradiction_of_continuousAt
    [ProperSpace E] {φ g : ℝ → E} {I : Set ℝ}
    (h_open : IsOpen I) (hI_nonempty : I.Nonempty) (hI_bddAbove : BddAbove I)
    (h_eq : EqOn φ g I)
    (h_exit_right : ∀ K : Set E, IsCompact K → BddAbove I →
      ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K)
    (hg_cont_at : ContinuousAt g (sSup I)) :
    False := by
  let x_sup := g (sSup I)
  let K : Set E := closedBall x_sup 1
  have hK : IsCompact K := isCompact_closedBall x_sup 1
  have h_exit := h_exit_right K hK hI_bddAbove
  rcases (eventually_nhdsLT_iff (a := sSup I) (p := fun t => t ∈ I → φ t ∉ K)).1 h_exit with
      ⟨l, hl, hl_prop⟩
  have hg_tendsto : Tendsto g (𝓝 (sSup I)) (𝓝 x_sup) := by
    simpa [x_sup] using hg_cont_at
  have hg_tendsto' : Tendsto g (𝓝[<] sSup I) (𝓝 x_sup) :=
    hg_tendsto.mono_left nhdsWithin_le_nhds
  have hφ_tendsto : Tendsto φ (𝓝[<] sSup I ⊓ 𝓟 I) (𝓝 x_sup) := by
    have hg_tendsto'' : Tendsto g (𝓝[<] sSup I ⊓ 𝓟 I) (𝓝 x_sup) :=
      hg_tendsto'.mono_left inf_le_left
    have hEq : ∀ᶠ t in 𝓝[<] sSup I ⊓ 𝓟 I, g t = φ t := by
      refine (Filter.eventually_inf_principal).2 ?_
      exact Filter.Eventually.of_forall (fun t ht => (h_eq ht).symm)
    exact hg_tendsto''.congr' hEq
  have hφ_in_K : ∀ᶠ t in 𝓝[<] sSup I ⊓ 𝓟 I, φ t ∈ K := by
    exact hφ_tendsto (Metric.closedBall_mem_nhds x_sup one_pos)
  have hφ_in_K' : ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∈ K :=
    (Filter.eventually_inf_principal).1 hφ_in_K
  rcases (eventually_nhdsLT_iff (a := sSup I) (p := fun t => t ∈ I → φ t ∈ K)).1 hφ_in_K' with
      ⟨l', hl', hl'_prop⟩
  set l'' := max l l'
  have hl''_lt : l'' < sSup I := max_lt hl hl'
  rcases (lt_csSup_iff hI_bddAbove hI_nonempty).1 hl''_lt with ⟨t, htI, hlt⟩
  have ht_lt : t < sSup I := lt_csSup_of_mem_of_isOpen h_open hI_bddAbove htI
  have ht_in_both : l < t ∧ t < sSup I ∧ l' < t := by
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hlt, ht_lt, lt_of_le_of_lt (le_max_right _ _) hlt⟩
  exact (hl_prop t ⟨ht_in_both.1, ht_in_both.2.1⟩ htI)
    (hl'_prop t ⟨ht_in_both.2.2, ht_in_both.2.1⟩ htI)

omit [NormedSpace ℝ E] in
private theorem exit_left_contradiction_of_continuousAt
    [ProperSpace E] {φ g : ℝ → E} {I : Set ℝ}
    (h_open : IsOpen I) (hI_nonempty : I.Nonempty) (hI_bddBelow : BddBelow I)
    (h_eq : EqOn φ g I)
    (h_exit_left : ∀ K : Set E, IsCompact K → BddBelow I →
      ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K)
    (hg_cont_at : ContinuousAt g (sInf I)) :
    False := by
  let x_inf := g (sInf I)
  let K : Set E := closedBall x_inf 1
  have hK : IsCompact K := isCompact_closedBall x_inf 1
  have h_exit := h_exit_left K hK hI_bddBelow
  rcases (eventually_nhdsGT_iff (a := sInf I) (p := fun t => t ∈ I → φ t ∉ K)).1 h_exit with
      ⟨u, hu, hu_prop⟩
  have hg_tendsto : Tendsto g (𝓝 (sInf I)) (𝓝 x_inf) := by
    simpa [x_inf] using hg_cont_at
  have hg_tendsto' : Tendsto g (𝓝[>] sInf I) (𝓝 x_inf) :=
    hg_tendsto.mono_left nhdsWithin_le_nhds
  have hφ_tendsto : Tendsto φ (𝓝[>] sInf I ⊓ 𝓟 I) (𝓝 x_inf) := by
    have hg_tendsto'' : Tendsto g (𝓝[>] sInf I ⊓ 𝓟 I) (𝓝 x_inf) :=
      hg_tendsto'.mono_left inf_le_left
    have hEq : ∀ᶠ t in 𝓝[>] sInf I ⊓ 𝓟 I, g t = φ t := by
      refine (Filter.eventually_inf_principal).2 ?_
      exact Filter.Eventually.of_forall (fun t ht => (h_eq ht).symm)
    exact hg_tendsto''.congr' hEq
  have hφ_in_K : ∀ᶠ t in 𝓝[>] sInf I ⊓ 𝓟 I, φ t ∈ K := by
    exact hφ_tendsto (Metric.closedBall_mem_nhds x_inf one_pos)
  have hφ_in_K' : ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∈ K :=
    (Filter.eventually_inf_principal).1 hφ_in_K
  rcases (eventually_nhdsGT_iff (a := sInf I) (p := fun t => t ∈ I → φ t ∈ K)).1 hφ_in_K' with
      ⟨u', hu', hu'_prop⟩
  set u'' := min u u'
  have hu''_gt : sInf I < u'' := lt_min hu hu'
  rcases (csInf_lt_iff hI_bddBelow hI_nonempty).1 hu''_gt with ⟨t, htI, hlt⟩
  have ht_gt : sInf I < t := csInf_lt_of_mem_of_isOpen h_open hI_bddBelow htI
  have ht_in_both : sInf I < t ∧ t < u ∧ t < u' := by
    have hlt_u : t < u := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlt_u' : t < u' := lt_of_lt_of_le hlt (min_le_right _ _)
    exact ⟨ht_gt, hlt_u, hlt_u'⟩
  exact (hu_prop t ⟨ht_in_both.1, ht_in_both.2.1⟩ htI)
    (hu'_prop t ⟨ht_in_both.1, ht_in_both.2.2⟩ htI)

/--
**Converse to compact-exit: leaving compacts implies maximality.**

If a solution leaves every compact subset of `E` near both endpoints (whenever they are finite),
then it cannot be extended further, hence is maximal.

This is the converse to the compact-exit lemmas: while those show that maximal solutions must
eventually leave compacts, this shows that a solution with this exit property must be maximal.
-/
theorem IsMaximalODESolutionWithin.of_leavesEveryCompact
    [ProperSpace E]
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h_curve : IsIntegralCurveOn φ (extendVectorField U v) I)
    (h_mapsTo : ∀ t ∈ I, (t, φ t) ∈ U)
    (h_open : IsOpen I) (h_conn : IsConnected I)
    (h_exit_right : ∀ K : Set E, IsCompact K → BddAbove I →
      ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K)
    (h_exit_left : ∀ K : Set E, IsCompact K → BddBelow I →
      ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K)
    (h_locLip0 : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    IsMaximalODESolutionWithin U v φ I := by
  let v : ℝ → E → E := extendVectorField U v
  have h_curve : IsIntegralCurveOn φ v I := by simpa [v] using h_curve
  have _h_locLip : LocallyLipschitz (fun p : ℝ × E => v p.1 p.2) := by
    simpa [v] using h_locLip0
  have hmax : IsMaximalODESolution v φ I := by
    refine
      { isConnected_domain := h_conn
        isOpen_domain := h_open
        isIntegralCurveOn := h_curve
        isMaximal := by
          intro g J h_g_curve h_J_open h_J_conn h_sub h_eq
          by_contra h_ne
          have h_ssub : I ⊂ J := HasSubset.Subset.ssubset_of_ne h_sub h_ne
          rcases Set.exists_of_ssubset h_ssub with ⟨t', ht'J, ht'nI⟩
          have hI_nonempty : I.Nonempty := h_conn.nonempty
          have hg_cont : ContinuousOn g J := h_g_curve.continuousOn
          by_cases h_above : ∀ t ∈ I, t < t'
          · have hI_bddAbove : BddAbove I := ⟨t', fun t ht => le_of_lt (h_above t ht)⟩
            have ht'_ge : sSup I ≤ t' := csSup_le hI_nonempty (fun t ht => le_of_lt (h_above t ht))
            let t₀ := hI_nonempty.some
            have ht₀ : t₀ ∈ I := hI_nonempty.some_mem
            by_cases ht'_eq : sSup I = t'
            · have hsSup_in_J : sSup I ∈ J := ht'_eq ▸ ht'J
              have hg_cont_at : ContinuousAt g (sSup I) :=
                hg_cont.continuousAt (h_J_open.mem_nhds hsSup_in_J)
              exact exit_right_contradiction_of_continuousAt
                (h_open := h_open) (hI_nonempty := hI_nonempty) (hI_bddAbove := hI_bddAbove)
                (h_eq := h_eq) (h_exit_right := h_exit_right) hg_cont_at
            · have hJ_ord : OrdConnected J := h_J_conn.isPreconnected.ordConnected
              have ht₀_in_J : t₀ ∈ J := h_sub ht₀
              have hIcc_sub : Icc t₀ t' ⊆ J := hJ_ord.out ht₀_in_J ht'J
              have hsSup_in_Icc : sSup I ∈ Icc t₀ t' := by
                constructor
                · exact le_csSup hI_bddAbove ht₀
                · exact ht'_ge
              have hsSup_in_J : sSup I ∈ J := hIcc_sub hsSup_in_Icc
              have hg_cont_at : ContinuousAt g (sSup I) :=
                hg_cont.continuousAt (h_J_open.mem_nhds hsSup_in_J)
              exact exit_right_contradiction_of_continuousAt
                (h_open := h_open) (hI_nonempty := hI_nonempty) (hI_bddAbove := hI_bddAbove)
                (h_eq := h_eq) (h_exit_right := h_exit_right) hg_cont_at
          · push_neg at h_above
            rcases h_above with ⟨t_up, ht_up_I, ht'_le_t_up⟩
            by_cases h_below : ∀ t ∈ I, t' < t
            · have hI_bddBelow : BddBelow I := ⟨t', fun t ht => le_of_lt (h_below t ht)⟩
              have ht'_le_inf : t' ≤ sInf I := by
                exact le_csInf hI_nonempty (fun t ht => le_of_lt (h_below t ht))
              have hJ_ord : OrdConnected J := h_J_conn.isPreconnected.ordConnected
              have ht_up_in_J : t_up ∈ J := h_sub ht_up_I
              have hIcc_sub : Icc t' t_up ⊆ J := hJ_ord.out ht'J ht_up_in_J
              have hsInf_in_Icc : sInf I ∈ Icc t' t_up := by
                constructor
                · exact ht'_le_inf
                · exact csInf_le hI_bddBelow ht_up_I
              have hsInf_in_J : sInf I ∈ J := hIcc_sub hsInf_in_Icc
              have hg_cont_at : ContinuousAt g (sInf I) :=
                hg_cont.continuousAt (h_J_open.mem_nhds hsInf_in_J)
              exact exit_left_contradiction_of_continuousAt
                (h_open := h_open) (hI_nonempty := hI_nonempty) (hI_bddBelow := hI_bddBelow)
                (h_eq := h_eq) (h_exit_left := h_exit_left) hg_cont_at
            · push_neg at h_below
              rcases h_below with ⟨t_lo, ht_lo_I, ht_lo_le_t'⟩
              have hI_ord : OrdConnected I := h_conn.isPreconnected.ordConnected
              have hIcc_sub : Icc t_lo t_up ⊆ I := hI_ord.out ht_lo_I ht_up_I
              have ht'_in_Icc : t' ∈ Icc t_lo t_up := ⟨ht_lo_le_t', ht'_le_t_up⟩
              have ht'_in_I : t' ∈ I := hIcc_sub ht'_in_Icc
              exact ht'nI ht'_in_I }
  refine ⟨?_, h_mapsTo⟩
  simpa [v] using hmax

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem eventually_prod_exit_right_of_snd_exit_right
    {φ : ℝ → E} {I : Set ℝ} {K : Set (ℝ × E)}
    (hEvent : ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ (Prod.snd '' K)) :
    ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → (t, φ t) ∉ K := by
  refine hEvent.mono ?_
  intro t ht htI htK
  apply ht htI
  exact ⟨(t, φ t), htK, rfl⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem eventually_prod_exit_left_of_snd_exit_left
    {φ : ℝ → E} {I : Set ℝ} {K : Set (ℝ × E)}
    (hEvent : ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ (Prod.snd '' K)) :
    ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → (t, φ t) ∉ K := by
  refine hEvent.mono ?_
  intro t ht htI htK
  apply ht htI
  exact ⟨(t, φ t), htK, rfl⟩

private theorem preimage_compact_subset_time_strip
    {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ} {K : Set (ℝ × E)} {lL lR : ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddAbove I) (hI' : BddBelow I)
    (hR : ∀ t, lR < t ∧ t < sSup I → t ∈ I → (t, φ t) ∉ K)
    (hL : ∀ t, sInf I < t ∧ t < lL → t ∈ I → (t, φ t) ∉ K) :
    {t : I | (t.1, φ t.1) ∈ K} ⊆ ((Subtype.val : I → ℝ) ⁻¹' Icc lL lR) := by
  intro t htA
  have htI : ((t : I) : ℝ) ∈ I := t.property
  have ht_lt : ((t : I) : ℝ) < sSup I := lt_csSup_of_mem_of_isOpen h.isOpen_domain hI htI
  have ht_gt : sInf I < ((t : I) : ℝ) := csInf_lt_of_mem_of_isOpen h.isOpen_domain hI' htI
  have ht_le : ((t : I) : ℝ) ≤ lR := by
    by_contra hlt
    have hlt' : lR < ((t : I) : ℝ) := lt_of_not_ge hlt
    exact (hR (((t : I) : ℝ)) ⟨hlt', ht_lt⟩ htI) htA
  have ht_ge : lL ≤ ((t : I) : ℝ) := by
    by_contra hlt
    have hlt' : ((t : I) : ℝ) < lL := lt_of_not_ge hlt
    exact (hL (((t : I) : ℝ)) ⟨ht_gt, hlt'⟩ htI) htA
  exact ⟨ht_ge, ht_le⟩

/--
**Properness of the extended curve (time-dependent, joint locally Lipschitz).**

If the maximal solution has finite endpoints and the uniform existence hypotheses hold on both
ends, then the extended curve `t ↦ (t, φ t)` has compact preimages of compact sets.
-/
theorem IsMaximalODESolutionWithin.isProperExtendedCurve_time_dependent_locallyLipschitz
    {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {φ : ℝ → E} {I : Set ℝ}
    (h0 : IsMaximalODESolutionWithin U v φ I) (hI : BddAbove I) (hI' : BddBelow I)
    (hI_nonempty : I.Nonempty)
    (h_uniform_right0 : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_uniform_left0 : ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
      ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≥] sInf I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt α ((extendVectorField U v) t (α t)) t)
    (h_locLip0 : LocallyLipschitz (fun p : ℝ × E => (extendVectorField U v) p.1 p.2)) :
    IsProperExtendedCurve φ I := by
  let v : ℝ → E → E := extendVectorField U v
  let h : IsMaximalODESolution v φ I := by
    simpa [v] using h0.toIsMaximal
  have h_uniform_right :
      ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
        ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
          α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t := by
    intro K' hK'
    simpa [v] using h_uniform_right0 K' hK'
  have h_uniform_left :
      ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
        ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≥] sInf I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
          α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t := by
    intro K' hK'
    simpa [v] using h_uniform_left0 K' hK'
  have h_locLip : LocallyLipschitz (fun p : ℝ × E => v p.1 p.2) := by
    simpa [v] using h_locLip0
  intro K hK
  let K' : Set E := Prod.snd '' K
  have hK' : IsCompact K' := hK.image continuous_snd
  have hEventR' :=
    IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually
      (h0 := h0) hI K' hK'
      (by
        intro K'' hK''
        simpa using h_uniform_right K'' hK'')
      (by simpa using h_locLip)
  have hEventR :
      ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → (t, φ t) ∉ K :=
    eventually_prod_exit_right_of_snd_exit_right (φ := φ) (I := I) (K := K) hEventR'
  have hEventL' :=
    IsMaximalODESolutionWithin.leavesEveryCompact_left_time_dependent_locallyLipschitz_eventually
      (h0 := h0) hI' hI_nonempty K' hK'
      (by
        intro K'' hK''
        simpa using h_uniform_left K'' hK'')
      (by simpa using h_locLip)
  have hEventL :
      ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → (t, φ t) ∉ K :=
    eventually_prod_exit_left_of_snd_exit_left (φ := φ) (I := I) (K := K) hEventL'
  rcases (eventually_nhdsLT_iff (a:=sSup I)
    (p:=fun t => t ∈ I → (t, φ t) ∉ K)).1 hEventR with ⟨lR, hlR, hR⟩
  rcases (eventually_nhdsGT_iff (a:=sInf I)
    (p:=fun t => t ∈ I → (t, φ t) ∉ K)).1 hEventL with ⟨lL, hlL, hL⟩
  let coeI : I → ℝ := Subtype.val
  let A : Set I := {t | (coeI t, φ t) ∈ K}
  have hφ_cont : Continuous (fun t : I => φ t) := (h.isIntegralCurveOn.continuousOn).restrict
  have hcont : Continuous (fun t : I => (coeI t, φ t)) :=
    (continuous_subtype_val : Continuous coeI).prodMk hφ_cont
  have hA_closed : IsClosed A := by
    have hK_closed : IsClosed K := hK.isClosed
    simpa [A] using hK_closed.preimage hcont
  have hA_sub : A ⊆ (coeI ⁻¹' Icc lL lR) := by
    simpa [A, coeI] using
      (preimage_compact_subset_time_strip (h := h) hI hI' (K := K) (lL := lL) (lR := lR) hR hL)
  have hIcc_sub : Icc lL lR ⊆ I := by
    rcases (csInf_lt_iff hI' hI_nonempty).1 hlL with ⟨tL, htL, htL_lt⟩
    rcases (lt_csSup_iff hI hI_nonempty).1 hlR with ⟨tR, htR, htR_lt⟩
    have hI_ord : OrdConnected I := h.isConnected_domain.isPreconnected.ordConnected
    have hIcc_tLtR : Icc tL tR ⊆ I := by
      intro x hx
      exact hI_ord.out htL htR hx
    have hIcc_sub' : Icc lL lR ⊆ Icc tL tR := by
      intro x hx
      have hL : tL ≤ lL := le_of_lt htL_lt
      have hR : lR ≤ tR := le_of_lt htR_lt
      exact ⟨hL.trans hx.1, hx.2.trans hR⟩
    intro x hx
    exact hIcc_tLtR (hIcc_sub' hx)
  have hImage : ((coeI) '' (coeI ⁻¹' Icc lL lR) : Set ℝ) = Icc lL lR := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x, hIcc_sub hx⟩, hx, rfl⟩
  have hIcc_compact : IsCompact (coeI ⁻¹' Icc lL lR) := by
    have hIcc_compact' : IsCompact (Icc lL lR) := isCompact_Icc
    have hImage_compact : IsCompact ((coeI) '' (coeI ⁻¹' Icc lL lR) : Set ℝ) := by
      simpa [hImage] using hIcc_compact'
    exact (Subtype.isCompact_iff (p:=fun t => t ∈ I)
      (s:=coeI ⁻¹' Icc lL lR)).2 hImage_compact
  exact IsCompact.of_isClosed_subset hIcc_compact hA_closed hA_sub

/-! ### Proper-space corollaries

The proper-space assumption is needed to turn norm bounds into compact sets: in
infinite-dimensional normed spaces, closed balls are not compact, so compact-exit does not imply
norm blow-up without `[ProperSpace E]`.
-/

private theorem not_bddAbove_of_linear_growth_within_univ
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h0 : IsMaximalODESolutionWithin
      (U := (Set.univ : Set (ℝ × E)))
      (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f p.1.2) φ I)
    (hI_nonempty : I.Nonempty) (hf : LocallyLipschitz f)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h_growth : ∀ x : E, ‖f x‖ ≤ K * ‖x‖ + C) :
    ¬ BddAbove I := by
  let h : IsMaximalODESolution (fun _ => f) φ I :=
    (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f) (f := φ) (I := I)).1 h0
  intro hI
  rcases hI_nonempty with ⟨t0, ht0⟩
  have hI_nonempty' : I.Nonempty := ⟨t0, ht0⟩
  have ht_lt_sup : ∀ {t : ℝ}, t ∈ I → t < sSup I := by
    intro t htI
    exact lt_csSup_of_mem_of_isOpen h.isOpen_domain hI htI
  have ht0_lt : t0 < sSup I := ht_lt_sup ht0
  let R : ℝ := gronwallBound ‖φ t0‖ K C (sSup I - t0)
  have h_bound : ∀ t ∈ I, t0 ≤ t → ‖φ t‖ ≤ R := by
    intro t htI ht0t
    have hI_ord : OrdConnected I := h.isConnected_domain.isPreconnected.ordConnected
    have hIcc : Icc t0 t ⊆ I := by
      intro x hx
      exact hI_ord.out ht0 htI hx
    have hcont : ContinuousOn φ (Icc t0 t) := h.isIntegralCurveOn.continuousOn.mono hIcc
    have hderiv :
        ∀ x ∈ Ico t0 t, HasDerivWithinAt φ (f (φ x)) (Ici x) x := by
      intro x hx
      have hxI : x ∈ I := hIcc ⟨hx.1, le_of_lt hx.2⟩
      have h' := (h.isIntegralCurveOn x hxI).hasDerivAt (h.isOpen_domain.mem_nhds hxI)
      exact h'.hasDerivWithinAt
    have hG := norm_le_gronwallBound_of_norm_deriv_right_le
      hcont hderiv (by exact le_rfl)
      (by
        intro x hx
        simpa using h_growth (φ x))
    have hG' : ‖φ t‖ ≤ gronwallBound ‖φ t0‖ K C (t - t0) :=
      hG t ⟨ht0t, le_rfl⟩
    have hmono : Monotone (gronwallBound ‖φ t0‖ K C) :=
      gronwallBound_mono (hδ:=by exact norm_nonneg _) hC hK
    have ht_le : t ≤ sSup I := le_csSup hI htI
    exact hG'.trans (hmono (sub_le_sub_right ht_le _))
  have hBoundEvent :
      ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∈ closedBall (0 : E) R := by
    refine (eventually_nhdsLT_iff (a := sSup I)
      (p := fun t => t ∈ I → φ t ∈ closedBall (0 : E) R)).2 ?_
    refine ⟨t0, ht0_lt, ?_⟩
    intro t ht htI
    have hnorm_le := h_bound t htI (le_of_lt ht.1)
    simpa [mem_closedBall, dist_eq_norm] using hnorm_le
  let vU : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} → E := fun p => f p.1.2
  have hWithin : IsMaximalODESolutionWithin (U := (Set.univ : Set (ℝ × E))) vU φ I :=
    by
      simpa [vU] using
        (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f) (f := φ) (I := I)).2 h
  have h_uniform :
      ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
        ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
          α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
            HasDerivAt α
              ((extendVectorField (U := (Set.univ : Set (ℝ × E))) vU) t (α t)) t := by
    intro K' hK'
    rcases uniform_time_of_existence_autonomous_compact_locallyLipschitz (hf:=hf) hK' with
      ⟨ε, hε, H⟩
    refine ⟨ε, hε, Filter.Eventually.of_forall ?_⟩
    intro t₀ ht₀ x hx
    rcases H x hx t₀ with ⟨α, hαt₀, hα⟩
    refine ⟨α, hαt₀, ?_⟩
    intro t ht
    simpa [vU, extendVectorField] using hα t ht
  have h_locLip_snd : LocallyLipschitz (Prod.snd : ℝ × E → E) :=
    (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × E → E)).locallyLipschitz
  have h_locLip_prod : LocallyLipschitz (fun p : ℝ × E => f p.2) := by
    simpa [Function.comp] using (LocallyLipschitz.comp hf h_locLip_snd)
  have h_locLip_ext :
      LocallyLipschitz (fun p : ℝ × E =>
        (extendVectorField (U := (Set.univ : Set (ℝ × E))) vU) p.1 p.2) := by
    simpa [vU, extendVectorField] using h_locLip_prod
  have hExit :=
    IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually
      (h0 := hWithin) hI (K := closedBall (0 : E) R) (isCompact_closedBall _ _)
      h_uniform h_locLip_ext
  rcases (eventually_nhdsLT_iff (a := sSup I)
    (p := fun t => t ∈ I → φ t ∉ closedBall (0 : E) R)).1 hExit with
    ⟨l_exit, hl_exit, h_exit⟩
  rcases (eventually_nhdsLT_iff (a := sSup I)
    (p := fun t => t ∈ I → φ t ∈ closedBall (0 : E) R)).1 hBoundEvent with
    ⟨l_bound, hl_bound, h_bound_ev⟩
  set l := max l_exit l_bound
  have hl : l < sSup I := max_lt_iff.mpr ⟨hl_exit, hl_bound⟩
  rcases (lt_csSup_iff (s := I) hI hI_nonempty').1 hl with ⟨t, htI, hlt⟩
  have ht_lt : t < sSup I := lt_csSup_of_mem_of_isOpen h.isOpen_domain hI htI
  have ht_exit : l_exit < t := lt_of_le_of_lt (le_max_left _ _) hlt
  have ht_bound : l_bound < t := lt_of_le_of_lt (le_max_right _ _) hlt
  have h_out := h_exit t ⟨ht_exit, ht_lt⟩ htI
  have h_in := h_bound_ev t ⟨ht_bound, ht_lt⟩ htI
  exact h_out h_in

private theorem not_bddBelow_of_linear_growth_within_univ
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h0 : IsMaximalODESolutionWithin
      (U := (Set.univ : Set (ℝ × E)))
      (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f p.1.2) φ I)
    (hI_nonempty : I.Nonempty) (hf : LocallyLipschitz f)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h_growth : ∀ x : E, ‖f x‖ ≤ K * ‖x‖ + C) :
    ¬ BddBelow I := by
  let h : IsMaximalODESolution (fun _ => f) φ I :=
    (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f) (f := φ) (I := I)).1 h0
  intro hI
  let f_rev : E → E := fun x => -f x
  let φ_rev : ℝ → E := φ ∘ Neg.neg
  let I_rev : Set ℝ := Neg.neg ⁻¹' I
  have h_rev : IsMaximalODESolution (fun _ => f_rev) φ_rev I_rev := by
    simpa [f_rev, φ_rev, I_rev] using (comp_neg_iff (v := fun _ => f) (f := φ) (I := I)).mpr h
  have hI_rev_nonempty : I_rev.Nonempty := by
    rcases hI_nonempty with ⟨t, ht⟩
    exact ⟨-t, by simpa [I_rev] using ht⟩
  have hf_rev : LocallyLipschitz f_rev := by
    have h_neg : LocallyLipschitz (fun x : E => -x) :=
      (LipschitzWith.id.neg : LipschitzWith 1 (fun x : E => -x)).locallyLipschitz
    simpa [f_rev, Function.comp] using (LocallyLipschitz.comp h_neg hf)
  have h_growth_rev : ∀ x : E, ‖f_rev x‖ ≤ K * ‖x‖ + C := by
    intro x
    simpa [f_rev] using h_growth x
  have hI_rev_bdd : BddAbove I_rev := BddAbove_preimage_neg hI
  have h0_rev : IsMaximalODESolutionWithin
      (U := (Set.univ : Set (ℝ × E)))
      (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f_rev p.1.2) φ_rev I_rev :=
    (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f_rev)
      (f := φ_rev) (I := I_rev)).2 h_rev
  exact not_bddAbove_of_linear_growth_within_univ
    (h0 := h0_rev) hI_rev_nonempty hf_rev hK hC h_growth_rev hI_rev_bdd

/--
**Global existence from linear growth (proper spaces).**

If `f` has linear growth and `φ` is a maximal solution of `x' = f x`, then the domain is unbounded
both above and below.

This is the standard ODE “no finite-time blow-up under linear growth” conclusion: in a proper
(hence locally compact) complete space, a maximal solution cannot have a finite endpoint if the
vector field grows at most linearly.
-/
theorem IsMaximalODESolutionWithin.global_existence_of_linear_growth
  [CompleteSpace E] [ProperSpace E]
  {f : E → E} {φ : ℝ → E} {I : Set ℝ}
  (h0 : IsMaximalODESolutionWithin
    (U := (Set.univ : Set (ℝ × E)))
    (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f p.1.2) φ I)
  (hI_nonempty : I.Nonempty)
  (hf : LocallyLipschitz f)
  {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
  (h_growth : ∀ x : E, ‖f x‖ ≤ K * ‖x‖ + C) :
  ¬ BddAbove I ∧ ¬ BddBelow I := by
  exact ⟨
    not_bddAbove_of_linear_growth_within_univ (h0 := h0) hI_nonempty hf hK hC h_growth,
    not_bddBelow_of_linear_growth_within_univ (h0 := h0) hI_nonempty hf hK hC h_growth
  ⟩


omit [NormedSpace ℝ E] in
private theorem isCompact_trapped_set
    [ProperSpace E] {U : Set E} (hU : IsOpen U) {R δ : ℝ} (hδ : 0 < δ) :
    IsCompact {x : E | x ∈ U ∧ ‖x‖ ≤ R ∧ δ ≤ infDist x Uᶜ} := by
  let K : Set E := {x | x ∈ U ∧ ‖x‖ ≤ R ∧ δ ≤ infDist x Uᶜ}
  let K0 : Set E := {x : E | ‖x‖ ≤ R} ∩ {x : E | δ ≤ infDist x Uᶜ}
  have hK_eq : K = K0 := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · simpa using hx.2.1
      · simpa using hx.2.2
    · intro hx
      have hx_norm : ‖x‖ ≤ R := by simpa using hx.1
      have hx_dist : δ ≤ infDist x Uᶜ := by simpa using hx.2
      have hxU : x ∈ U := by
        have hballU : ball x (infDist x Uᶜ) ⊆ U := by
          simpa using (ball_infDist_compl_subset (s := U) (x := x))
        have hballU' : ball x δ ⊆ U := by
          intro y hy
          exact hballU ((ball_subset_ball hx_dist) hy)
        exact hballU' (mem_ball_self hδ)
      exact ⟨hxU, hx_norm, hx_dist⟩
  have hU_closed : IsClosed Uᶜ := isClosed_compl_iff.mpr hU
  have hcont : Continuous fun x : E => infDist x Uᶜ := by
    have hcont' : Continuous fun x : E => infDist x (closure Uᶜ) :=
      continuous_infDist_pt (s := closure Uᶜ)
    simpa [hU_closed.closure_eq] using hcont'
  have hK0_closed : IsClosed K0 := by
    have h1 : IsClosed {x : E | ‖x‖ ≤ R} := isClosed_le continuous_norm continuous_const
    have h2 : IsClosed {x : E | δ ≤ infDist x Uᶜ} := isClosed_le continuous_const hcont
    simpa [K0] using h1.inter h2
  have hK0_sub : K0 ⊆ closedBall (0 : E) R := by
    intro x hx
    have hx_norm : ‖x‖ ≤ R := by simpa using hx.1
    simpa [mem_closedBall, dist_eq_norm] using hx_norm
  have hK0_bounded : Bornology.IsBounded K0 :=
    (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : E) R)).subset hK0_sub
  have hK0_compact : IsCompact K0 := isCompact_of_isClosed_isBounded hK0_closed hK0_bounded
  simpa [K, hK_eq] using hK0_compact

omit [NormedSpace ℝ E] in
private theorem eventually_escape_disjunction_of_exit_compact
    {φ : ℝ → E} {I : Set ℝ} {U : Set E} {R δ : ℝ}
    (h_subset : ∀ t ∈ I, φ t ∈ U)
    (hEvent : ∀ᶠ t in 𝓝[<] sSup I, t ∈ I →
      φ t ∉ {x : E | x ∈ U ∧ ‖x‖ ≤ R ∧ δ ≤ infDist x Uᶜ}) :
    ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → (R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ) := by
  refine hEvent.mono ?_
  intro t ht htI
  have h_in_U : φ t ∈ U := h_subset t htI
  have ht_not' : ¬ (‖φ t‖ ≤ R ∧ δ ≤ infDist (φ t) Uᶜ) := by
    intro hKcond
    exact ht htI ⟨h_in_U, hKcond.1, hKcond.2⟩
  have ht_or : ¬ (‖φ t‖ ≤ R) ∨ ¬ (δ ≤ infDist (φ t) Uᶜ) := not_and_or.mp ht_not'
  exact ht_or.elim (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))

private theorem contradiction_of_trapped_assumptions_at_eventual_point
    {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ} {U : Set E} {R δ l : ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    (hl : l < sSup I)
    (hl_prop : ∀ t, l < t ∧ t < sSup I → t ∈ I →
      (R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ))
    (h_bound : ∀ t ∈ I, ‖φ t‖ ≤ R)
    (h_dist : ∀ t ∈ I, δ ≤ infDist (φ t) Uᶜ) :
    False := by
  rcases (lt_csSup_iff hI hI_nonempty).1 hl with ⟨t, htI, hlt⟩
  have ht_lt : t < sSup I := lt_csSup_of_mem_of_isOpen h.isOpen_domain hI htI
  have hescape := hl_prop t ⟨hlt, ht_lt⟩ htI
  have hnot_norm : ¬ R < ‖φ t‖ := not_lt_of_ge (h_bound t htI)
  have hnot_dist : ¬ infDist (φ t) Uᶜ < δ := not_lt_of_ge (h_dist t htI)
  exact hescape.elim hnot_norm hnot_dist

/--
**Trapping/invariance corollary (proper spaces).**

If the solution stays in an open set `U`, is norm-bounded, and remains a positive distance from
`Uᶜ`, then the right endpoint cannot be finite.

Heuristically: if the trajectory remains in a compact subset of `U`, then maximality forces the
time domain to be unbounded above.
-/
theorem IsMaximalODESolutionWithin.not_bddAbove_of_trapped
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ} {U : Set E}
    (h0 : IsMaximalODESolutionWithin
      (U := (Set.univ : Set (ℝ × E)))
      (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => f p.1.2) φ I)
    (hI_nonempty : I.Nonempty) (hf : LocallyLipschitz f)
    (hU : IsOpen U) (h_subset : ∀ t ∈ I, φ t ∈ U)
    {R δ : ℝ} (hδ : 0 < δ)
    (h_bound : ∀ t ∈ I, ‖φ t‖ ≤ R)
    (h_dist : ∀ t ∈ I, δ ≤ infDist (φ t) Uᶜ) :
    ¬ BddAbove I := by
  let h : IsMaximalODESolution (fun _ => f) φ I :=
    (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f) (f := φ) (I := I)).1 h0
  intro hI
  let K : Set E := {x : E | x ∈ U ∧ ‖x‖ ≤ R ∧ δ ≤ infDist x Uᶜ}
  have hK_compact : IsCompact K := by
    simpa [K] using isCompact_trapped_set (U := U) hU (R := R) (δ := δ) hδ
  have hEscape :
      ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → (R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ) := by
    let vU : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} → E := fun p => f p.1.2
    have hWithin : IsMaximalODESolutionWithin (U := (Set.univ : Set (ℝ × E))) vU φ I :=
      by
        simpa [vU] using
          (IsMaximalODESolutionWithin.univ_iff (v := fun _ => f) (f := φ) (I := I)).2 h
    have h_uniform :
        ∀ K' : Set E, IsCompact K' → ∃ ε : ℝ,
          ε > 0 ∧ ∀ᶠ t₀ in 𝓝[≤] sSup I, t₀ ∈ I → ∀ x ∈ K', ∃ α : ℝ → E,
            α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
              HasDerivAt α ((extendVectorField (U := (Set.univ : Set (ℝ × E))) vU) t (α t)) t := by
      intro K' hK'
      rcases uniform_time_of_existence_autonomous_compact_locallyLipschitz (hf:=hf) hK' with
        ⟨ε, hε, H⟩
      refine ⟨ε, hε, Filter.Eventually.of_forall ?_⟩
      intro t₀ ht₀ x hx
      rcases H x hx t₀ with ⟨α, hαt₀, hα⟩
      refine ⟨α, hαt₀, ?_⟩
      intro t ht
      simpa [vU, extendVectorField] using hα t ht
    have h_locLip_snd : LocallyLipschitz (Prod.snd : ℝ × E → E) :=
      (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × E → E)).locallyLipschitz
    have h_locLip_prod : LocallyLipschitz (fun p : ℝ × E => f p.2) := by
      simpa [Function.comp] using (LocallyLipschitz.comp hf h_locLip_snd)
    have h_locLip_ext :
        LocallyLipschitz (fun p : ℝ × E =>
          (extendVectorField (U := (Set.univ : Set (ℝ × E))) vU) p.1 p.2) := by
      simpa [vU, extendVectorField] using h_locLip_prod
    have hEvent :=
      IsMaximalODESolutionWithin.leavesEveryCompact_right_time_dependent_locallyLipschitz_eventually
        (h0 := hWithin) hI (K := K) hK_compact h_uniform h_locLip_ext
    exact eventually_escape_disjunction_of_exit_compact (φ := φ) (I := I) (U := U) (R := R) (δ := δ)
      h_subset hEvent
  rcases (eventually_nhdsLT_iff (a:=sSup I)
    (p:=fun t => t ∈ I → (R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ))).1 hEscape with
    ⟨l, hl, hl_prop⟩
  exact contradiction_of_trapped_assumptions_at_eventual_point
    (h := h) hI hI_nonempty hl hl_prop h_bound h_dist
