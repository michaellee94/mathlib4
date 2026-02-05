/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Algebra.Order.Group.Bounds
public import Mathlib.Analysis.ODE.MaximalSolution
public import Mathlib.Analysis.ODE.Transform

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
- `IsMaximalODESolution.leavesEveryCompact_right_time_dependent_eventually`: time-dependent case
  with uniform existence hypotheses
- `IsMaximalODESolution.leavesEveryCompact_left_time_dependent_eventually`: time-dependent
  left-endpoint analog
- `IsMaximalODESolution.leavesEveryCompact_right_autonomous_eventually`: autonomous case, assuming
  uniform time-of-existence on compacts
- `IsMaximalODESolution.leavesEveryCompact_left_autonomous_eventually`: autonomous left-endpoint
  analog
- `IsMaximalODESolution.`
  `leavesEveryCompact_right_time_dependent_of_IsPicardLindelof_on_Icc_eventually`:
  time-dependent case with Picard–Lindelöf hypotheses on a time strip
- `IsMaximalODESolution.`
  `leavesEveryCompact_left_time_dependent_of_IsPicardLindelof_on_Icc_eventually`:
  left-endpoint analog on a time strip
- `IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt`: autonomous case with a
  global $C^1$ vector field
- `IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt`: left-endpoint analog
- `IsMaximalODESolution.unbounded_of_compact_bound_autonomous_of_contDiffAt`: global-existence
  criterion from a compact bound on the trajectory
- `IsMaximalODESolution.global_existence_of_linear_growth`: global existence from linear growth via
  Grönwall plus compact-exit
- `IsMaximalODESolution.not_bddAbove_of_trapped`: trapping/invariance corollary in proper spaces

We also provide autonomous uniform time-of-existence theorems.
For the time-dependent uniform existence input on a strip, see
`uniform_time_of_existence_time_dependent_compact_on_Icc` in `Mathlib.Analysis.ODE.PicardLindelof`.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology Pointwise

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section TimeReversalHelpers

variable {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ}

theorem IsMaximalODESolution.comp_neg_iff :
    IsMaximalODESolution (fun t x ↦ - v (-t) x) (f ∘ Neg.neg) (Neg.neg ⁻¹' I) ↔
    IsMaximalODESolution v f I := by
  constructor
  · intro h
    refine ⟨?_, ?_, IsIntegralCurveOn.comp_neg_iff.mp h.deriv, ?_⟩
    · simpa [preimage_neg_neg_set] using h.isOpen.preimage continuous_neg
    · exact ((Homeomorph.neg ℝ).isConnected_preimage (s:=I)).1 h.isConnected
    intro g J hg hJopen hJconn hIJ hEq
    have h_rev := h.is_maximal (g ∘ Neg.neg) (Neg.neg ⁻¹' J)
      (IsIntegralCurveOn.comp_neg_iff.mpr hg)
      (hJopen.preimage continuous_neg)
      (((Homeomorph.neg ℝ).isConnected_preimage (s:=J)).2 hJconn)
      (preimage_mono hIJ)
      (fun t ht ↦ by
        have ht' : -t ∈ I := by simpa using ht
        have hEq' : f (-t) = g (-t) := hEq (x:=-t) ht'
        simpa [Function.comp] using hEq')
    have h_rev' := congrArg (fun s => Neg.neg ⁻¹' s) h_rev
    simpa [preimage_neg_neg_set] using h_rev'
  · intro h
    refine ⟨?_, ?_, IsIntegralCurveOn.comp_neg_iff.mpr h.deriv, ?_⟩
    · simpa [preimage_neg_neg_set] using h.isOpen.preimage continuous_neg
    · exact ((Homeomorph.neg ℝ).isConnected_preimage (s:=I)).2 h.isConnected
    intro g J hg hJopen hJconn hIJ hEq
    have hg' : IsIntegralCurveOn (g ∘ Neg.neg) v (Neg.neg ⁻¹' J) := by
      have hg' :=
        (IsIntegralCurveOn.comp_neg_iff (v:=fun t x ↦ - v (-t) x) (γ:=g) (s:=J)).mpr hg
      simpa [Function.comp] using hg'
    have hEq' : EqOn f (g ∘ Neg.neg) I := by
      intro t ht
      have ht' : -t ∈ Neg.neg ⁻¹' I := by simpa
      have hEq'' : f t = g (-t) := by simpa [Function.comp] using hEq (x:=-t) ht'
      simpa [Function.comp] using hEq''
    have hIJ' : I ⊆ Neg.neg ⁻¹' J := by
      intro t ht
      have : -t ∈ J := hIJ (by simpa using ht)
      simpa using this
    have h_rev := h.is_maximal (g ∘ Neg.neg) (Neg.neg ⁻¹' J)
      hg'
      (hJopen.preimage continuous_neg)
      (((Homeomorph.neg ℝ).isConnected_preimage (s:=J)).2 hJconn)
      hIJ'
      hEq'
    have h_rev' := congrArg (fun s => Neg.neg ⁻¹' s) h_rev
    simpa [preimage_neg_neg_set] using h_rev'

end TimeReversalHelpers

section

variable [CompleteSpace E]

/--
**Uniform time of existence on a compact set (autonomous case).**

If `f` is $C^1$ on a compact set `K`, then there exists a uniform time window `ε > 0` such that
for every `x ∈ K` and every initial time `t₀`, there is a solution to `x' = f x` with
`α t₀ = x` defined on $(t₀-ε, t₀+ε)$.
-/
theorem uniform_time_of_existence_autonomous_compact
    {f : E → E} {K : Set E} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f x) :
    ∃ ε > (0 : ℝ), ∀ x ∈ K, ∀ t₀ : ℝ, ∃ α : ℝ → E,
      α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  classical
  by_cases hKempty : K = ∅
  · refine ⟨1, by norm_num, ?_⟩
    simp [hKempty]
  have hK_nonempty : K.Nonempty := by
    simpa [Set.nonempty_iff_ne_empty] using hKempty
  have hlocal : ∀ x ∈ K, ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ y ∈ closedBall x r, ∀ t₀ : ℝ, ∃ α : ℝ → E,
        α t₀ = y ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
    intro x hx
    obtain ⟨r, hr, ε, hε, H⟩ :=
      ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt (hf x hx)
        (0 : ℝ)
    refine ⟨r, hr, ε, hε, ?_⟩
    intro y hy t₀
    rcases H y hy with ⟨α, hα0, hα⟩
    refine ⟨fun t => α (t - t₀), ?_, ?_⟩
    · simp [hα0]
    · intro t ht
      have ht' : t - t₀ ∈ Ioo (0 - ε) (0 + ε) := by
        constructor <;> nlinarith [ht.1, ht.2]
      have hαderiv : HasDerivAt α (f (α (t - t₀))) (t - t₀) := hα (t - t₀) ht'
      have hshift : HasDerivAt (fun s => α (s - t₀)) (f (α (t - t₀))) t :=
        HasDerivAt.comp_sub_const (x:=t) (a:=t₀) hαderiv
      simpa using hshift
  choose r hr ε hε H using hlocal
  let r₀ : E → ℝ := fun x => if hx : x ∈ K then r x hx else 1
  let ε₀ : E → ℝ := fun x => if hx : x ∈ K then ε x hx else 1
  let U : E → Set E := fun x => ball x (r₀ x / 2)
  have hU : ∀ x ∈ K, U x ∈ 𝓝 x := by
    intro x hx
    have hr0 : 0 < r₀ x := by simpa [r₀, hx] using hr x hx
    have : (0 : ℝ) < r₀ x / 2 := by nlinarith [hr0]
    have hmem : ball x (r₀ x / 2) ∈ 𝓝 x := ball_mem_nhds _ this
    simpa [U] using hmem
  rcases hK.elim_nhds_subcover U hU with ⟨T, hTK, hcover⟩
  have hT_nonempty : T.Nonempty := by
    by_contra ht
    have ht_empty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hcover' : K ⊆ (∅ : Set E) := by simpa [ht_empty] using hcover
    rcases hK_nonempty with ⟨x, hx⟩
    exact (hcover' hx).elim
  let εmin : ℝ := (T.image (fun x => ε₀ x)).min' (Finset.image_nonempty.mpr hT_nonempty)
  have hεmin_pos : 0 < εmin := by
    have hmem : εmin ∈ T.image (fun x => ε₀ x) :=
      Finset.min'_mem (T.image fun x => ε₀ x) (Finset.image_nonempty.mpr hT_nonempty)
    rcases Finset.mem_image.mp hmem with ⟨x, hx_t, hx_eq⟩
    have hxK : x ∈ K := hTK x hx_t
    have hpos : 0 < ε x hxK := hε x hxK
    have hpos' : 0 < ε₀ x := by simpa [ε₀, hxK] using hpos
    simpa [hx_eq] using hpos'
  refine ⟨εmin, hεmin_pos, ?_⟩
  intro x hx t₀
  have hxcover : x ∈ ⋃ x ∈ T, U x := hcover hx
  rcases mem_iUnion.1 hxcover with ⟨x₀, hx₀⟩
  rcases mem_iUnion.1 hx₀ with ⟨hx₀t, hxU⟩
  have hx₀K : x₀ ∈ K := hTK x₀ hx₀t
  have hx_closed : x ∈ closedBall x₀ (r x₀ hx₀K) := by
    have hx_ball : x ∈ ball x₀ (r₀ x₀ / 2) := by simpa [U] using hxU
    have hsub : ball x₀ (r₀ x₀ / 2) ⊆ closedBall x₀ (r x₀ hx₀K) := by
      have hr0 : r₀ x₀ = r x₀ hx₀K := by simp [r₀, hx₀K]
      have hsub1 : ball x₀ (r x₀ hx₀K / 2) ⊆ closedBall x₀ (r x₀ hx₀K / 2) := by
        simpa using (ball_subset_closedBall :
          ball x₀ (r x₀ hx₀K / 2) ⊆ closedBall x₀ (r x₀ hx₀K / 2))
      have hsub2 : closedBall x₀ (r x₀ hx₀K / 2) ⊆ closedBall x₀ (r x₀ hx₀K) := by
        have : (r x₀ hx₀K / 2) ≤ r x₀ hx₀K := by nlinarith [hr x₀ hx₀K]
        exact closedBall_subset_closedBall this
      exact by simpa [hr0] using Set.Subset.trans hsub1 hsub2
    exact hsub hx_ball
  rcases H x₀ hx₀K x hx_closed t₀ with ⟨α, hαt₀, hα⟩
  refine ⟨α, hαt₀, ?_⟩
  intro t ht
  have hεle : εmin ≤ ε₀ x₀ := by
    have hximage : ε₀ x₀ ∈ T.image (fun x => ε₀ x) := by
      exact Finset.mem_image.mpr ⟨x₀, hx₀t, rfl⟩
    exact Finset.min'_le _ _ hximage
  have hεle' : εmin ≤ ε x₀ hx₀K := by simpa [ε₀, hx₀K] using hεle
  have ht' : t ∈ Ioo (t₀ - ε x₀ hx₀K) (t₀ + ε x₀ hx₀K) := by
    constructor <;> nlinarith [ht.1, ht.2, hεle']
  exact hα t ht'

/--
**Uniform time of existence on compact sets (autonomous case, global $C^1$).**

If `f` is $C^1$ everywhere, then every compact set admits a uniform time of existence.
-/
theorem uniform_time_of_existence_autonomous_compact_global
    {f : E → E} (hf : ∀ x : E, ContDiffAt ℝ 1 f x) {K : Set E} (hK : IsCompact K) :
    ∃ ε > (0 : ℝ), ∀ x ∈ K, ∀ t₀ : ℝ, ∃ α : ℝ → E,
      α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  uniform_time_of_existence_autonomous_compact (K:=K) hK (by intro x hx; exact hf x)


end

/--
**Right-endpoint compact-exit lemma (time-dependent, uniform existence hypothesis; eventual form).**

Under the uniform existence and Lipschitz hypotheses below, the solution is eventually outside
`K` as it approaches `sSup I` from the left.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_time_dependent_eventually
    {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddAbove I)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t)
    (K_const : NNReal) (h_lip : ∀ t : ℝ, LipschitzWith K_const (v t)) :
    ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K := by
  classical
  rcases h_uniform K hK with ⟨ε₀, hε₀, H⟩
  refine (eventually_nhdsLT_iff (a:=sSup I) (p:=fun t => t ∈ I → φ t ∉ K)).2 ?_
  refine ⟨sSup I - ε₀ / 2, ?_, ?_⟩
  · exact sub_lt_self _ (half_pos hε₀)
  · intro t ht htI
    by_contra htK
    rcases H (φ t) htK t htI with ⟨α, hαt, hα⟩
    let J : Set ℝ := I ∪ Ioo (t - ε₀) (t + ε₀)
    let g : ℝ → E := fun s => if s ∈ I then φ s else α s
    have hα_curve : IsIntegralCurveOn α v (Ioo (t - ε₀) (t + ε₀)) := by
      intro s hs
      exact (hα s hs).hasDerivWithinAt
    have h_eq_on : EqOn φ α (I ∩ Ioo (t - ε₀) (t + ε₀)) := by
      refine IsIntegralCurveOn.eqOn_of_agree_at_t₀_of_lipschitz (v:=v) (t₀:=t)
        h.deriv hα_curve h.isOpen (isOpen_Ioo) h.isConnected
        (isConnected_Ioo ?_) htI ?_ hαt.symm K_const ?_
      · nlinarith [hε₀]
      · exact ⟨by nlinarith [hε₀], by nlinarith [hε₀]⟩
      · intro t_val _
        exact h_lip t_val
    have hJ_open : IsOpen J := h.isOpen.union isOpen_Ioo
    have hJ_conn : IsConnected J := by
      have h_inter_nonempty : (I ∩ Ioo (t - ε₀) (t + ε₀)).Nonempty := by
        refine ⟨t, htI, ?_⟩
        exact ⟨by nlinarith [hε₀], by nlinarith [hε₀]⟩
      exact IsConnected.union h_inter_nonempty h.isConnected (isConnected_Ioo (by nlinarith [hε₀]))
    have hJ_curve : IsIntegralCurveOn g v J := by
      intro s hs
      by_cases hsI : s ∈ I
      · have hφ_deriv : HasDerivAt φ (v s (φ s)) s :=
          (h.deriv s hsI).hasDerivAt (h.isOpen.mem_nhds hsI)
        have h_eq : g =ᶠ[𝓝 s] φ := by
          filter_upwards [h.isOpen.mem_nhds hsI] with y hyI
          simp [g, hyI]
        have h' : HasDerivAt g (v s (g s)) s := by
          have h' := HasDerivAt.congr_of_eventuallyEq hφ_deriv h_eq
          simpa [g, hsI] using h'
        exact h'.hasDerivWithinAt
      · have hsIoo : s ∈ Ioo (t - ε₀) (t + ε₀) := hs.resolve_left hsI
        have hα_deriv : HasDerivAt α (v s (α s)) s := hα s hsIoo
        have h_eq : g =ᶠ[𝓝 s] α := by
          have hIoo_nhds : Ioo (t - ε₀) (t + ε₀) ∈ 𝓝 s :=
            isOpen_Ioo.mem_nhds hsIoo
          filter_upwards [hIoo_nhds] with y hyIoo
          by_cases hyI : y ∈ I
          · have : y ∈ I ∩ Ioo (t - ε₀) (t + ε₀) := ⟨hyI, hyIoo⟩
            have h_eq_on := h_eq_on this
            simp [g, hyI, h_eq_on]
          · simp [g, hyI]
        have h' : HasDerivAt g (v s (g s)) s := by
          have h' := HasDerivAt.congr_of_eventuallyEq hα_deriv h_eq
          simpa [g, hsI] using h'
        exact h'.hasDerivWithinAt
    have hEq : EqOn φ g I := by
      intro s hsI
      simp [g, hsI]
    have hsup : ∃ t', t' ∈ J ∧ sSup I < t' := by
      refine ⟨t + ε₀ / 2, ?_, ?_⟩
      · have : t + ε₀ / 2 ∈ Ioo (t - ε₀) (t + ε₀) := by
          constructor <;> nlinarith [hε₀]
        exact Or.inr this
      · have ht_close : sSup I - ε₀ / 2 < t := by
          nlinarith [ht.1]
        nlinarith [ht_close]
    rcases hsup with ⟨t', ht'J, ht'_sup⟩
    have h_eq : I = J := h.is_maximal g J hJ_curve hJ_open hJ_conn (subset_union_left) hEq
    have ht_le : t' ≤ sSup I := by
      have : t' ∈ I := by simpa [h_eq] using ht'J
      exact le_csSup hI this
    exact (not_lt_of_ge ht_le) ht'_sup

/--
**Left-endpoint compact-exit lemma (time-dependent, uniform existence hypothesis; eventual form).**

Under the uniform existence and Lipschitz hypotheses below, the solution is eventually outside
`K` as it approaches `sInf I` from the right.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_time_dependent_eventually
    {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t)
    (K_const : NNReal) (h_lip : ∀ t : ℝ, LipschitzWith K_const (v t)) :
    ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K := by
  let v_rev := fun t x ↦ - v (-t) x
  let f_rev := φ ∘ Neg.neg
  let I_rev := Neg.neg ⁻¹' I
  have h_rev : IsMaximalODESolution v_rev f_rev I_rev := IsMaximalODESolution.comp_neg_iff.mpr h
  have hI_rev_bdd : BddAbove I_rev := BddAbove_preimage_neg hI
  have h_rev_bound : sSup I_rev = -sInf I := by
     apply sSup_preimage_neg hI_nonempty hI
  have h_uniform' : ∀ K : Set E, IsCompact K → ∃ ε > 0, ∀ x ∈ K, ∀ t₀ ∈ I_rev, ∃ α,
      α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v_rev t (α t)) t := by
    intro K' hK'
    rcases h_uniform K' hK' with ⟨ε₀, hε₀, H⟩
    refine ⟨ε₀, hε₀, ?_⟩
    intro x hx t₀ ht₀
    rcases H x hx (-t₀) (by simpa using ht₀) with ⟨β, hβ0, hβ⟩
    refine ⟨β ∘ Neg.neg, by simp [hβ0], ?_⟩
    intro t ht
    have ht' : -t ∈ Ioo (-t₀ - ε₀) (-t₀ + ε₀) := by
      constructor <;> linarith [ht.1, ht.2]
    have hβ' : HasDerivAt β (v (-t) (β (-t))) (-t) := hβ (-t) ht'
    have hcomp := HasDerivAt.scomp (g₁:=β) (h:=Neg.neg) (x:=t)
      (g₁':=v (-t) (β (-t))) (h':=-1) hβ' (hasDerivAt_neg t)
    simpa [v_rev, Function.comp] using hcomp
  have h_lip' : ∀ t, LipschitzWith K_const (v_rev t) := by
    intro t
    have h' : LipschitzWith K_const (fun x => - v (-t) x) := (h_lip (-t)).neg
    simpa [v_rev] using h'
  have h_event_rev : ∀ᶠ t in 𝓝[<] sSup I_rev, t ∈ I_rev → f_rev t ∉ K :=
    IsMaximalODESolution.leavesEveryCompact_right_time_dependent_eventually
      h_rev hI_rev_bdd K hK h_uniform' K_const h_lip'
  have hl_rev : ∃ l < sSup I_rev, ∀ t, l < t ∧ t < sSup I_rev → (t ∈ I_rev → f_rev t ∉ K) :=
    (eventually_nhdsLT_iff (a:=sSup I_rev) (p:=fun t => t ∈ I_rev → f_rev t ∉ K)).1 h_event_rev
  rcases hl_rev with ⟨l, hl, hl_prop⟩
  refine (eventually_nhdsGT_iff (a:=sInf I) (p:=fun t => t ∈ I → φ t ∉ K)).2 ?_
  refine ⟨-l, ?_, ?_⟩
  · have : l < sSup I_rev := hl
    rw [h_rev_bound] at this
    linarith
  · intro t ht htI
    have ht' : l < -t ∧ -t < sSup I_rev := by
      have h1 : l < -t := by linarith [ht.2]
      have h2 : -t < sSup I_rev := by
        have : -t < -sInf I := by linarith [ht.1]
        simpa [h_rev_bound] using this
      exact ⟨h1, h2⟩
    have htI' : -t ∈ I_rev := by simpa [I_rev] using htI
    have hnot := hl_prop (-t) ht' htI'
    simpa [f_rev, Function.comp] using hnot

namespace IsMaximalODESolution

/--
**Right-endpoint compact-exit lemma (time-dependent, Picard–Lindelöf on a strip; eventual form).**

This is a wrapper around `IsMaximalODESolution.leavesEveryCompact_right_time_dependent_eventually`
using a uniform time-of-existence hypothesis obtained from Picard–Lindelöf on a time strip.
-/
theorem leavesEveryCompact_right_time_dependent_of_IsPicardLindelof_on_Icc_eventually
  [CompleteSpace E]
  {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ}
  (h : IsMaximalODESolution v φ I) (hI : BddAbove I)
    {tmin tmax tmin' tmax' : ℝ} (htmin : tmin < tmin') (htmax : tmax' < tmax)
    (hIcc : I ⊆ Icc tmin' tmax')
    (hpl : ∀ x : E, ∀ t₀ : Icc tmin tmax,
      ∃ a r L Kc : NNReal, IsPicardLindelof v (tmin:=tmin) (tmax:=tmax) t₀ x a r L Kc)
    (K : Set E) (hK : IsCompact K)
    (K_const : NNReal) (h_lip : ∀ t : ℝ, LipschitzWith K_const (v t)) :
    ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K := by
  have h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t := by
    intro K hK
    have hplK : ∀ x ∈ K, ∀ t₀ : Icc tmin tmax,
        ∃ a r L Kc : NNReal, IsPicardLindelof v (tmin:=tmin) (tmax:=tmax) t₀ x a r L Kc := by
      intro x hx t₀
      exact hpl x t₀
    rcases uniform_time_of_existence_time_dependent_compact_on_Icc
        (v:=v) (K:=K) (tmin:=tmin) (tmax:=tmax) (tmin':=tmin') (tmax':=tmax')
        htmin htmax hplK with ⟨ε, hε, H⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx t₀ ht₀
    have ht₀' : t₀ ∈ Icc tmin' tmax' := hIcc ht₀
    exact H x hx t₀ ht₀'
  exact IsMaximalODESolution.leavesEveryCompact_right_time_dependent_eventually
    (h:=h) hI K hK h_uniform K_const h_lip

/--
**Left-endpoint compact-exit lemma (time-dependent, Picard–Lindelöf on a strip; eventual form).**

This is a wrapper around `IsMaximalODESolution.leavesEveryCompact_left_time_dependent_eventually`
using a uniform time-of-existence hypothesis obtained from Picard–Lindelöf on a time strip.
-/
theorem leavesEveryCompact_left_time_dependent_of_IsPicardLindelof_on_Icc_eventually
  [CompleteSpace E]
  {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ}
  (h : IsMaximalODESolution v φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    {tmin tmax tmin' tmax' : ℝ} (htmin : tmin < tmin') (htmax : tmax' < tmax)
    (hIcc : I ⊆ Icc tmin' tmax')
    (hpl : ∀ x : E, ∀ t₀ : Icc tmin tmax,
      ∃ a r L Kc : NNReal, IsPicardLindelof v (tmin:=tmin) (tmax:=tmax) t₀ x a r L Kc)
    (K : Set E) (hK : IsCompact K)
    (K_const : NNReal) (h_lip : ∀ t : ℝ, LipschitzWith K_const (v t)) :
    ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K := by
  have h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t := by
    intro K hK
    have hplK : ∀ x ∈ K, ∀ t₀ : Icc tmin tmax,
        ∃ a r L Kc : NNReal, IsPicardLindelof v (tmin:=tmin) (tmax:=tmax) t₀ x a r L Kc := by
      intro x hx t₀
      exact hpl x t₀
    rcases uniform_time_of_existence_time_dependent_compact_on_Icc
        (v:=v) (K:=K) (tmin:=tmin) (tmax:=tmax) (tmin':=tmin') (tmax':=tmax')
        htmin htmax hplK with ⟨ε, hε, H⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx t₀ ht₀
    have ht₀' : t₀ ∈ Icc tmin' tmax' := hIcc ht₀
    exact H x hx t₀ ht₀'
  exact IsMaximalODESolution.leavesEveryCompact_left_time_dependent_eventually
    (h:=h) hI hI_nonempty K hK h_uniform K_const h_lip

end IsMaximalODESolution

/--
**Right-endpoint compact-exit lemma (autonomous, uniform existence hypothesis; eventual form).**

Under the uniform existence and locally Lipschitz hypotheses, the solution is eventually outside
`K` as it approaches `sSup I` from the left.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_autonomous_eventually
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t)
    (h_locLip : LocallyLipschitz f) :
    ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K := by
  classical
  rcases h_uniform K hK with ⟨ε₀, hε₀, H⟩
  refine (eventually_nhdsLT_iff (a:=sSup I) (p:=fun t => t ∈ I → φ t ∉ K)).2 ?_
  refine ⟨sSup I - ε₀ / 2, sub_lt_self _ (half_pos hε₀), ?_⟩
  intro t ht htI
  by_contra htK
  rcases H (φ t) htK t htI with ⟨α, hαt, hα⟩
  have hα_curve : IsIntegralCurveOn α (fun _ => f) (Ioo (t - ε₀) (t + ε₀)) := by
    intro s hs
    exact (hα s hs).hasDerivWithinAt
  have h_eq_on : EqOn φ α (I ∩ Ioo (t - ε₀) (t + ε₀)) := by
    let K_int : Set ℝ := I ∩ Ioo (t - ε₀) (t + ε₀)
    have hK_open : IsOpen K_int := h.isOpen.inter isOpen_Ioo
    have htK_int : t ∈ K_int := ⟨htI, by constructor <;> linarith [hε₀]⟩
    have hK_conn : IsConnected K_int := by
      have hI_ord : OrdConnected I := h.isConnected.isPreconnected.ordConnected
      have hIoo_ord : OrdConnected (Ioo (t - ε₀) (t + ε₀)) := ordConnected_Ioo
      have hK_ord : OrdConnected K_int := OrdConnected.inter hI_ord hIoo_ord
      exact ⟨⟨t, htK_int⟩, hK_ord.isPreconnected⟩
    have hlocal : ∀ s ∈ K_int, φ s = α s → φ =ᶠ[𝓝 s] α := by
      intro s hs h_eq
      rcases h_locLip (φ s) with ⟨Kc, U, hU, hLipU⟩
      have hLip : ∀ᶠ t' in 𝓝 s, LipschitzOnWith Kc (fun x => f x) U :=
        Filter.Eventually.of_forall (fun _ => hLipU)
      have hφ_cont : ContinuousAt φ s := by
        have hderiv := (h.deriv s hs.1).hasDerivAt (h.isOpen.mem_nhds hs.1)
        exact hderiv.continuousAt
      have hα_cont : ContinuousAt α s := (hα s hs.2).continuousAt
      have hφ_mem : ∀ᶠ t' in 𝓝 s, φ t' ∈ U := hφ_cont.preimage_mem_nhds hU
      have hα_mem : ∀ᶠ t' in 𝓝 s, α t' ∈ U := by
        have hU' : U ∈ 𝓝 (α s) := by simpa [h_eq] using hU
        exact hα_cont.preimage_mem_nhds hU'
      have hI_mem : ∀ᶠ t' in 𝓝 s, t' ∈ I := h.isOpen.mem_nhds hs.1
      have hIoo_mem : ∀ᶠ u in 𝓝 s, u ∈ Ioo (t - ε₀) (t + ε₀) := isOpen_Ioo.mem_nhds hs.2
      have hφ_deriv : ∀ᶠ u in 𝓝 s, HasDerivAt φ (f (φ u)) u := by
        refine hI_mem.mono ?_
        intro u huI
        exact (h.deriv u huI).hasDerivAt (h.isOpen.mem_nhds huI)
      have hα_deriv : ∀ᶠ u in 𝓝 s, HasDerivAt α (f (α u)) u := by
        refine hIoo_mem.mono ?_
        intro u huIoo
        exact hα u huIoo
      have hφ_ev : ∀ᶠ u in 𝓝 s, HasDerivAt φ (f (φ u)) u ∧ φ u ∈ U := hφ_deriv.and hφ_mem
      have hα_ev : ∀ᶠ u in 𝓝 s, HasDerivAt α (f (α u)) u ∧ α u ∈ U := hα_deriv.and hα_mem
      exact ODE_solution_unique_of_eventually (v:=fun _ => f) (s:=fun _ => U) hLip hφ_ev hα_ev
        (by simp [h_eq])
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
    have hφ_cont_on : ContinuousOn φ K_int := h.deriv.continuousOn.mono (fun _ hx => hx.1)
    have hα_cont_on : ContinuousOn α K_int := hα_curve.continuousOn.mono (fun _ hx => hx.2)
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
        exact (closure_subtype (x:=⟨x, hxK⟩) (s:=S')).2 this
      have hxS' : (⟨x, hxK⟩ : {t' // t' ∈ K_int}) ∈ S' := hS'closed.closure_subset hx'
      exact ⟨hxK, hxS'⟩
    have hK_preconn : IsPreconnected K_int := hK_conn.isPreconnected
    have hS_nonempty : (K_int ∩ S).Nonempty := ⟨t, htK_int, htK_int, by simp [hαt]⟩
    have hsubset : K_int ⊆ S :=
      hK_preconn.subset_of_closure_inter_subset hS_open hS_nonempty hS_closure
    intro s hs
    exact (hsubset hs).2
  have hJ_open : IsOpen (I ∪ Ioo (t - ε₀) (t + ε₀)) := h.isOpen.union isOpen_Ioo
  have hJ_conn : IsConnected (I ∪ Ioo (t - ε₀) (t + ε₀)) := by
    have h_inter_nonempty : (I ∩ Ioo (t - ε₀) (t + ε₀)).Nonempty :=
      ⟨t, htI, by constructor <;> linarith [hε₀]⟩
    exact IsConnected.union h_inter_nonempty h.isConnected (isConnected_Ioo (by linarith [hε₀]))
  let g : ℝ → E := fun s => if s ∈ I then φ s else α s
  have hJ_curve : IsIntegralCurveOn g (fun _ => f) (I ∪ Ioo (t - ε₀) (t + ε₀)) := by
    intro s hs
    by_cases hsI : s ∈ I
    · have hφ_deriv : HasDerivAt φ (f (φ s)) s := (h.deriv s hsI).hasDerivAt (h.isOpen.mem_nhds hsI)
      have h_eq : g =ᶠ[𝓝 s] φ := by filter_upwards [h.isOpen.mem_nhds hsI] with y hyI; simp [g, hyI]
      have h' : HasDerivAt g (f (g s)) s := by
        have h' := HasDerivAt.congr_of_eventuallyEq hφ_deriv h_eq
        simpa [g, hsI] using h'
      exact h'.hasDerivWithinAt
    · have hsIoo : s ∈ Ioo (t - ε₀) (t + ε₀) := hs.resolve_left hsI
      have hα_deriv : HasDerivAt α (f (α s)) s := hα s hsIoo
      have h_eq : g =ᶠ[𝓝 s] α := by
        have hIoo_nhds : Ioo (t - ε₀) (t + ε₀) ∈ 𝓝 s := isOpen_Ioo.mem_nhds hsIoo
        filter_upwards [hIoo_nhds] with y hyIoo
        by_cases hyI : y ∈ I
        · have : y ∈ I ∩ Ioo (t - ε₀) (t + ε₀) := ⟨hyI, hyIoo⟩
          have h_eq_on := h_eq_on this
          simp [g, hyI, h_eq_on]
        · simp [g, hyI]
      have h' : HasDerivAt g (f (g s)) s := by
        have h' := HasDerivAt.congr_of_eventuallyEq hα_deriv h_eq
        simpa [g, hsI] using h'
      exact h'.hasDerivWithinAt
  have hEq : EqOn φ g I := fun s hsI => by simp [g, hsI]
  have hsup : ∃ t', t' ∈ I ∪ Ioo (t - ε₀) (t + ε₀) ∧ sSup I < t' := by
    refine ⟨t + ε₀ / 2, Or.inr ⟨by linarith [hε₀], by linarith [hε₀]⟩, ?_⟩
    have ht_close : sSup I - ε₀ / 2 < t := by linarith [ht.1]
    linarith [ht_close]
  rcases hsup with ⟨t', ht'J, ht'_sup⟩
  have h_eq : I = I ∪ Ioo (t - ε₀) (t + ε₀) :=
    h.is_maximal g _ hJ_curve hJ_open hJ_conn subset_union_left hEq
  have ht_le : t' ≤ sSup I := by
    have : t' ∈ I := by rw [h_eq]; exact ht'J
    exact le_csSup hI this
  exact (not_lt_of_ge ht_le) ht'_sup

/--
**Left-endpoint compact-exit lemma (autonomous, uniform existence hypothesis; eventual form).**

Under the uniform existence and locally Lipschitz hypotheses, the solution is eventually outside
`K` as it approaches `sInf I` from the right.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_autonomous_eventually
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t)
    (h_locLip : LocallyLipschitz f) :
    ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K := by
  -- Use time reversal to reduce to the right-endpoint case
  let f_rev := fun x => - f x
  let φ_rev := φ ∘ Neg.neg
  let I_rev := Neg.neg ⁻¹' I
  have h_rev : IsMaximalODESolution (fun _ => f_rev) φ_rev I_rev :=
    IsMaximalODESolution.comp_neg_iff.mpr h
  have hI_rev_bdd : BddAbove I_rev := BddAbove_preimage_neg hI
  have h_rev_bound : sSup I_rev = -sInf I := sSup_preimage_neg hI_nonempty hI
  have h_uniform' : ∀ K : Set E, IsCompact K → ∃ ε > 0, ∀ x ∈ K, ∀ t₀ ∈ I_rev, ∃ α,
      α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f_rev (α t)) t := by
    intro K' hK'
    rcases h_uniform K' hK' with ⟨ε₀, hε₀, H⟩
    refine ⟨ε₀, hε₀, ?_⟩
    intro x hx t₀ ht₀
    rcases H x hx (-t₀) (by simpa using ht₀) with ⟨β, hβ0, hβ⟩
    refine ⟨β ∘ Neg.neg, by simp [hβ0], ?_⟩
    intro t ht
    have ht' : -t ∈ Ioo (-t₀ - ε₀) (-t₀ + ε₀) := by constructor <;> linarith [ht.1, ht.2]
    have hβ' : HasDerivAt β (f (β (-t))) (-t) := hβ (-t) ht'
    have hcomp := HasDerivAt.scomp (g₁:=β) (h:=Neg.neg) (x:=t)
      (g₁':=f (β (-t))) (h':=-1) hβ' (hasDerivAt_neg t)
    simpa [f_rev, Function.comp] using hcomp
  have h_locLip' : LocallyLipschitz f_rev := h_locLip.neg
  have h_event_rev : ∀ᶠ t in 𝓝[<] sSup I_rev, t ∈ I_rev → φ_rev t ∉ K :=
    IsMaximalODESolution.leavesEveryCompact_right_autonomous_eventually
      h_rev hI_rev_bdd K hK h_uniform' h_locLip'
  have hl_rev : ∃ l < sSup I_rev, ∀ t, l < t ∧ t < sSup I_rev → (t ∈ I_rev → φ_rev t ∉ K) :=
    (eventually_nhdsLT_iff (a:=sSup I_rev) (p:=fun t => t ∈ I_rev → φ_rev t ∉ K)).1 h_event_rev
  rcases hl_rev with ⟨l, hl, hl_prop⟩
  refine (eventually_nhdsGT_iff (a:=sInf I) (p:=fun t => t ∈ I → φ t ∉ K)).2 ?_
  refine ⟨-l, ?_, ?_⟩
  · have : l < sSup I_rev := hl
    rw [h_rev_bound] at this
    linarith
  · intro t ht htI
    have ht' : l < -t ∧ -t < sSup I_rev := by
      have h1 : l < -t := by linarith [ht.2]
      have h2 : -t < sSup I_rev := by
        have : -t < -sInf I := by linarith [ht.1]
        simpa [h_rev_bound] using this
      exact ⟨h1, h2⟩
    have htI' : -t ∈ I_rev := by simpa [I_rev] using htI
    have hnot := hl_prop (-t) ht' htI'
    simpa [φ_rev, Function.comp] using hnot

/--
**Right-endpoint compact-exit lemma (autonomous, global $C^1$; eventual form).**

If `f` is $C^1$ everywhere, then a maximal solution to `x' = f x` is eventually outside every
compact set as it approaches `sSup I` from the left, i.e.
`∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K`.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K := by
  have hf_contDiff : ContDiff ℝ 1 f := contDiff_iff_contDiffAt.mpr hf
  have h_locLip : LocallyLipschitz f := hf_contDiff.locallyLipschitz
  have h_uniform : ∀ K : Set E, IsCompact K → ∃ ε > 0, ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α,
      α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
    intro K' hK'
    rcases uniform_time_of_existence_autonomous_compact_global hf hK' with ⟨ε, hε, H⟩
    exact ⟨ε, hε, fun x hx t₀ _ => H x hx t₀⟩
  exact leavesEveryCompact_right_autonomous_eventually h hI K hK h_uniform h_locLip

/--
**Left-endpoint compact-exit lemma (autonomous, global $C^1$; eventual form).**

If `f` is $C^1$ everywhere, then a maximal solution to `x' = f x` is eventually outside every
compact set as it approaches `sInf I` from the right, i.e.
`∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K`.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K := by
  have hf_contDiff : ContDiff ℝ 1 f := contDiff_iff_contDiffAt.mpr hf
  have h_locLip : LocallyLipschitz f := hf_contDiff.locallyLipschitz
  have h_uniform : ∀ K : Set E, IsCompact K → ∃ ε > 0, ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α,
      α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
    intro K' hK'
    rcases uniform_time_of_existence_autonomous_compact_global hf hK' with ⟨ε, hε, H⟩
    exact ⟨ε, hε, fun x hx t₀ _ => H x hx t₀⟩
  exact leavesEveryCompact_left_autonomous_eventually h hI hI_nonempty K hK h_uniform h_locLip

/--
**Global existence criterion (two-sided unboundedness).**

If a maximal autonomous solution with a global $C^1$ vector field stays inside a compact set,
then its domain is unbounded both above and below.
-/
theorem IsMaximalODESolution.unbounded_of_compact_bound_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (htraj : ∀ t ∈ I, φ t ∈ K) :
    ¬ BddAbove I ∧ ¬ BddBelow I := by
  refine ⟨?_, ?_⟩
  · intro hI
    have hEvent := IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
      (h:=h) hI K hK hf
    have hnot : ¬ ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∉ K := by
      intro h_event
      rcases (eventually_nhdsLT_iff (a:=sSup I) (p:=fun t => t ∈ I → φ t ∉ K)).1 h_event with
        ⟨l, hl, hl_prop⟩
      rcases (lt_csSup_iff hI hI_nonempty).1 hl with ⟨t, htI, hlt⟩
      have ht_lt : t < sSup I := by
        have hnhds : I ∈ 𝓝 t := h.isOpen.mem_nhds htI
        rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hball⟩
        have hhalf : 0 < δ / 2 := by nlinarith [hδpos]
        have ht_in_ball : t + δ / 2 ∈ Metric.ball t δ := by
          have hhalf_lt : δ / 2 < δ := by nlinarith [hδpos]
          have hdist_lt : dist (t + δ / 2) t < δ := by
            have h_abs : |δ| / 2 < δ := by
              simpa [abs_of_pos hδpos] using hhalf_lt
            simpa [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_abs
          exact hdist_lt
        have ht_in_I : t + δ / 2 ∈ I := hball ht_in_ball
        have hlt' : t < t + δ / 2 := by nlinarith [hδpos]
        have ht_le : t + δ / 2 ≤ sSup I := le_csSup hI ht_in_I
        exact lt_of_lt_of_le hlt' ht_le
      have hcontra := hl_prop t ⟨hlt, ht_lt⟩ htI
      exact hcontra (htraj t htI)
    exact hnot hEvent
  · intro hI
    have hEvent := IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
      (h:=h) hI hI_nonempty K hK hf
    have hnot : ¬ ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → φ t ∉ K := by
      intro h_event
      rcases (eventually_nhdsGT_iff (a:=sInf I) (p:=fun t => t ∈ I → φ t ∉ K)).1 h_event with
        ⟨u, hu, hu_prop⟩
      rcases (csInf_lt_iff hI hI_nonempty).1 hu with ⟨t, htI, ht_lt_u⟩
      have hnhds : I ∈ 𝓝 t := h.isOpen.mem_nhds htI
      rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hball⟩
      set δ' : ℝ := min (δ / 2) ((u - t) / 2)
      have hδ'pos : 0 < δ' := by
        have h1 : 0 < δ / 2 := by nlinarith [hδpos]
        have h2 : 0 < (u - t) / 2 := by nlinarith [ht_lt_u]
        exact lt_min h1 h2
      have hδ'le : δ' ≤ (u - t) / 2 := min_le_right _ _
      have hδ'lt : δ' < δ := by
        have hle : δ' ≤ δ / 2 := min_le_left _ _
        have hlt : (δ / 2) < δ := by nlinarith [hδpos]
        exact lt_of_le_of_lt hle hlt
      have ht_in_ball : t + δ' ∈ Metric.ball t δ := by
        have hdist_lt : dist (t + δ') t < δ := by
          have h_abs : |δ'| < δ := by
            have h_abs' : |δ'| = δ' := abs_of_pos hδ'pos
            simpa [h_abs'] using hδ'lt
          simpa [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_abs
        exact hdist_lt
      have ht' : t + δ' ∈ I := hball ht_in_ball
      have ht'_lt_u : t + δ' < u := by
        nlinarith [hδ'le]
      have ht'_gt : sInf I < t + δ' := by
        have ht_le : sInf I ≤ t := csInf_le hI htI
        have hlt : t < t + δ' := by nlinarith [hδ'pos]
        exact lt_of_le_of_lt ht_le hlt
      have hcontra := hu_prop (t + δ') ⟨ht'_gt, ht'_lt_u⟩ ht'
      exact hcontra (htraj (t + δ') ht')
    exact hnot hEvent

/-! ### Proper-space corollaries

The proper-space assumption is needed to turn norm bounds into compact sets: in
infinite-dimensional normed spaces, closed balls are not compact, so compact-exit does not imply
norm blow-up without `[ProperSpace E]`.
-/

/--
**Global existence from linear growth (proper spaces).**

If `f` has linear growth and `φ` is a maximal solution of `x' = f x`, then the domain is unbounded
both above and below.
-/
theorem IsMaximalODESolution.global_existence_of_linear_growth
  [CompleteSpace E] [ProperSpace E]
  {f : E → E} {φ : ℝ → E} {I : Set ℝ}
  (h : IsMaximalODESolution (fun _ => f) φ I) (hI_nonempty : I.Nonempty)
  (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
  {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
  (h_growth : ∀ x : E, ‖f x‖ ≤ K * ‖x‖ + C) :
  ¬ BddAbove I ∧ ¬ BddBelow I := by
    classical
    have not_bddAbove_of_linear_growth :
        ∀ {f : E → E} {φ : ℝ → E} {I : Set ℝ},
          IsMaximalODESolution (fun _ => f) φ I → I.Nonempty →
          (∀ x : E, ContDiffAt ℝ 1 f x) → (0 ≤ K) → (0 ≤ C) →
          (∀ x : E, ‖f x‖ ≤ K * ‖x‖ + C) → ¬ BddAbove I := by
      intro f φ I h hI_nonempty0 hf hK hC h_growth hI
      rcases hI_nonempty0 with ⟨t0, ht0⟩
      have ht0_lt : t0 < sSup I := by
        have hnhds : I ∈ 𝓝 t0 := h.isOpen.mem_nhds ht0
        rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hball⟩
        have ht' : t0 + δ / 2 ∈ I := by
          have hhalf_lt : δ / 2 < δ := by nlinarith [hδpos]
          have hdist_lt : dist (t0 + δ / 2) t0 < δ := by
            have h_abs : |δ| / 2 < δ := by
              simpa [abs_of_pos hδpos] using hhalf_lt
            simpa [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_abs
          exact hball hdist_lt
        have hlt : t0 < t0 + δ / 2 := by nlinarith [hδpos]
        have ht'_le : t0 + δ / 2 ≤ sSup I := le_csSup hI ht'
        exact lt_of_lt_of_le hlt ht'_le
      let R : ℝ := gronwallBound ‖φ t0‖ K C (sSup I - t0)
      have h_bound : ∀ t ∈ I, t0 ≤ t → ‖φ t‖ ≤ R := by
        intro t htI ht0t
        have hI_ord : OrdConnected I := h.isConnected.isPreconnected.ordConnected
        have hIcc : Icc t0 t ⊆ I := by
          intro x hx
          exact hI_ord.out ht0 htI hx
        have hcont : ContinuousOn φ (Icc t0 t) := h.deriv.continuousOn.mono hIcc
        have hderiv :
            ∀ x ∈ Ico t0 t, HasDerivWithinAt φ (f (φ x)) (Ici x) x := by
          intro x hx
          have hxI : x ∈ I := hIcc ⟨hx.1, le_of_lt hx.2⟩
          have h' := (h.deriv x hxI).hasDerivAt (h.isOpen.mem_nhds hxI)
          exact h'.hasDerivWithinAt
        have hbound :
            ∀ x ∈ Ico t0 t, ‖f (φ x)‖ ≤ K * ‖φ x‖ + C := by
          intro x hx
          simpa using h_growth (φ x)
        have hG := norm_le_gronwallBound_of_norm_deriv_right_le
          hcont hderiv (by exact le_rfl) hbound
        have hG' : ‖φ t‖ ≤ gronwallBound ‖φ t0‖ K C (t - t0) :=
          hG t ⟨ht0t, le_rfl⟩
        have hmono : Monotone (gronwallBound ‖φ t0‖ K C) :=
          gronwallBound_mono (hδ:=by exact norm_nonneg _) hC hK
        have hle : gronwallBound ‖φ t0‖ K C (t - t0) ≤
            gronwallBound ‖φ t0‖ K C (sSup I - t0) := by
          have ht_le : t ≤ sSup I := le_csSup hI htI
          exact hmono (sub_le_sub_right ht_le _)
        exact hG'.trans hle
      have hBoundEvent :
          ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → φ t ∈ closedBall (0 : E) R := by
        refine (eventually_nhdsLT_iff (a:=sSup I)
          (p:=fun t => t ∈ I → φ t ∈ closedBall (0 : E) R)).2 ?_
        refine ⟨t0, ht0_lt, ?_⟩
        intro t ht htI
        have hnorm_le := h_bound t htI (le_of_lt ht.1)
        simpa [mem_closedBall, dist_eq_norm] using hnorm_le
      have hExit := IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
        (h:=h) hI (K:=closedBall (0 : E) R) (isCompact_closedBall _ _) hf
      rcases (eventually_nhdsLT_iff (a:=sSup I)
        (p:=fun t => t ∈ I → φ t ∉ closedBall (0 : E) R)).1 hExit with
        ⟨l_exit, hl_exit, h_exit⟩
      rcases (eventually_nhdsLT_iff (a:=sSup I)
        (p:=fun t => t ∈ I → φ t ∈ closedBall (0 : E) R)).1 hBoundEvent with
        ⟨l_bound, hl_bound, h_bound_ev⟩
      set l := max l_exit l_bound
      have hl : l < sSup I := max_lt_iff.mpr ⟨hl_exit, hl_bound⟩
      have hI_nonempty' : I.Nonempty := ⟨t0, ht0⟩
      rcases (lt_csSup_iff (s:=I) hI hI_nonempty').1 hl with ⟨t, htI, hlt⟩
      have ht_lt : t < sSup I := by
        have hnhds : I ∈ 𝓝 t := h.isOpen.mem_nhds htI
        rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hball⟩
        have ht' : t + δ / 2 ∈ I := by
          have hhalf_lt : δ / 2 < δ := by nlinarith [hδpos]
          have hdist_lt : dist (t + δ / 2) t < δ := by
            have h_abs : |δ| / 2 < δ := by
              simpa [abs_of_pos hδpos] using hhalf_lt
            simpa [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_abs
          exact hball hdist_lt
        have hlt' : t < t + δ / 2 := by nlinarith [hδpos]
        have ht'_le : t + δ / 2 ≤ sSup I := le_csSup hI ht'
        exact lt_of_lt_of_le hlt' ht'_le
      have ht_exit : l_exit < t := lt_of_le_of_lt (le_max_left _ _) hlt
      have ht_bound : l_bound < t := lt_of_le_of_lt (le_max_right _ _) hlt
      have h_out := h_exit t ⟨ht_exit, ht_lt⟩ htI
      have h_in := h_bound_ev t ⟨ht_bound, ht_lt⟩ htI
      exact h_out h_in
    have h_not_bddAbove : ¬ BddAbove I :=
      not_bddAbove_of_linear_growth (f:=f) (φ:=φ) (I:=I) h hI_nonempty hf hK hC h_growth
    have h_not_bddBelow : ¬ BddBelow I := by
      intro hI
      let f_rev : E → E := fun x => - f x
      let φ_rev : ℝ → E := φ ∘ Neg.neg
      let I_rev : Set ℝ := Neg.neg ⁻¹' I
      have h_rev : IsMaximalODESolution (fun _ => f_rev) φ_rev I_rev :=
        IsMaximalODESolution.comp_neg_iff.mpr h
      have hI_rev_nonempty : I_rev.Nonempty := by
        rcases hI_nonempty with ⟨t, ht⟩
        exact ⟨-t, by simpa [I_rev] using ht⟩
      have hf_rev : ∀ x : E, ContDiffAt ℝ 1 f_rev x := by
        intro x
        simpa [f_rev] using (hf x).neg
      have h_growth_rev : ∀ x : E, ‖f_rev x‖ ≤ K * ‖x‖ + C := by
        intro x
        simpa [f_rev] using h_growth x
      have hI_rev_bdd : BddAbove I_rev := BddAbove_preimage_neg hI
      exact
        not_bddAbove_of_linear_growth (f:=f_rev) (φ:=φ_rev) (I:=I_rev) h_rev
          hI_rev_nonempty hf_rev hK hC h_growth_rev hI_rev_bdd
    exact ⟨h_not_bddAbove, h_not_bddBelow⟩

/--
**Finite-time blow-up (right, proper spaces; eventual form).**

If `E` is a proper space, then compact-exit implies that the norm is eventually above any
prescribed bound near a finite right endpoint.
-/
theorem IsMaximalODESolution.norm_unbounded_right_autonomous_of_contDiffAt
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∀ R : ℝ, ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → R < ‖φ t‖ := by
  intro R
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall _ _
  have hEvent := IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    (h:=h) hI (K:=closedBall (0 : E) R) hK hf
  refine hEvent.mono ?_
  intro t ht htI
  have hdist : R < dist (φ t) 0 := by
    have : ¬ dist (φ t) 0 ≤ R := by
      intro hle
      exact ht htI (by simpa [mem_closedBall] using hle)
    exact lt_of_not_ge this
  have hnorm : R < ‖φ t‖ := by
    simpa [dist_eq_norm] using hdist
  exact hnorm

/--
**Finite-time blow-up (right, proper spaces; tendsto form).**

In a proper space, the norm of a maximal solution with a global $C^1$ vector field tends to
$+\infty$ along the within-domain left-neighborhood filter `𝓝[<] sSup I ⊓ 𝓟 I`.
-/
theorem IsMaximalODESolution.tendsto_norm_right_autonomous_of_contDiffAt
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    Tendsto (fun t => ‖φ t‖) (𝓝[<] sSup I ⊓ 𝓟 I) atTop := by
  refine tendsto_atTop.2 ?_
  intro R
  have hEvent := IsMaximalODESolution.norm_unbounded_right_autonomous_of_contDiffAt
    (h:=h) hI hf R
  have hEvent' : ∀ᶠ t in 𝓝[<] sSup I ⊓ 𝓟 I, R < ‖φ t‖ :=
    (eventually_inf_principal).2 hEvent
  exact hEvent'.mono fun _ ht => le_of_lt ht

/--
**Finite-time blow-up (left, proper spaces; eventual form).**

If `E` is a proper space, then compact-exit implies that the norm is eventually above any
prescribed bound near a finite left endpoint.
-/
theorem IsMaximalODESolution.norm_unbounded_left_autonomous_of_contDiffAt
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∀ R : ℝ, ∀ᶠ t in 𝓝[>] sInf I, t ∈ I → R < ‖φ t‖ := by
  intro R
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall _ _
  have hEvent := IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty (K:=closedBall (0 : E) R) hK hf
  refine hEvent.mono ?_
  intro t ht htI
  have hdist : R < dist (φ t) 0 := by
    have : ¬ dist (φ t) 0 ≤ R := by
      intro hle
      exact ht htI (by simpa [mem_closedBall] using hle)
    exact lt_of_not_ge this
  have hnorm : R < ‖φ t‖ := by
    simpa [dist_eq_norm] using hdist
  exact hnorm

/--
**Finite-time blow-up (left, proper spaces; tendsto form).**

In a proper space, the norm of a maximal solution with a global $C^1$ vector field tends to
$+\infty$ along the within-domain right-neighborhood filter `𝓝[>] sInf I ⊓ 𝓟 I`.
-/
theorem IsMaximalODESolution.tendsto_norm_left_autonomous_of_contDiffAt
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    Tendsto (fun t => ‖φ t‖) (𝓝[>] sInf I ⊓ 𝓟 I) atTop := by
  refine tendsto_atTop.2 ?_
  intro R
  have hEvent := IsMaximalODESolution.norm_unbounded_left_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty hf R
  have hEvent' : ∀ᶠ t in 𝓝[>] sInf I ⊓ 𝓟 I, R < ‖φ t‖ :=
    (eventually_inf_principal).2 hEvent
  exact hEvent'.mono fun _ ht => le_of_lt ht

/--
**Escape lemma (proper spaces; eventual form).**

Let `U` be an open set and assume a maximal solution stays in `U`.
Near a finite right endpoint, the solution must eventually either:
* escape every fixed norm bound, or
* get within any prescribed distance of `Uᶜ`.

Formally, for any `R` and any `δ > 0`:
`∀ᶠ t in 𝓝[<] sSup I, t ∈ I → (R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ)`.
-/
theorem IsMaximalODESolution.norm_unbounded_or_dist_boundary_tendsto_zero_of_properSpace
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ} {U : Set E}
  (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (hU : IsOpen U) (h_subset : ∀ t ∈ I, φ t ∈ U) :
    ∀ R : ℝ, ∀ δ > 0,
      ∀ᶠ t in 𝓝[<] sSup I, t ∈ I → (R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ) := by
  classical
  intro R δ hδ
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
          simpa using (ball_infDist_compl_subset (s:=U) (x:=x))
        have hballU' : ball x δ ⊆ U := by
          intro y hy
          apply hballU
          exact (ball_subset_ball hx_dist) hy
        exact hballU' (mem_ball_self hδ)
      exact ⟨hxU, hx_norm, hx_dist⟩
  have hU_closed : IsClosed Uᶜ := isClosed_compl_iff.mpr hU
  have hcont : Continuous fun x : E => infDist x Uᶜ := by
    have hcont' : Continuous fun x : E => infDist x (closure Uᶜ) :=
      continuous_infDist_pt (s:=closure Uᶜ)
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
  have hK_compact : IsCompact K := by
    simpa [hK_eq] using hK0_compact
  have hEvent := IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    (h:=h) hI (K:=K) hK_compact hf
  refine hEvent.mono ?_
  intro t ht htI
  have h_in_U : φ t ∈ U := h_subset t htI
  have ht_not' : ¬ (‖φ t‖ ≤ R ∧ δ ≤ infDist (φ t) Uᶜ) := by
    intro hKcond
    exact ht htI ⟨h_in_U, hKcond.1, hKcond.2⟩
  have ht_disj : R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ := by
    have ht_or : ¬ (‖φ t‖ ≤ R) ∨ ¬ (δ ≤ infDist (φ t) Uᶜ) :=
      not_and_or.mp ht_not'
    exact ht_or.elim (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact ht_disj

/--
**Trapping/invariance corollary (proper spaces).**

If the solution stays in an open set `U`, is norm-bounded, and remains a positive distance from
`Uᶜ`, then the right endpoint cannot be finite.
-/
theorem IsMaximalODESolution.not_bddAbove_of_trapped
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ} {U : Set E}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI_nonempty : I.Nonempty)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (hU : IsOpen U) (h_subset : ∀ t ∈ I, φ t ∈ U)
    {R δ : ℝ} (hδ : 0 < δ)
    (h_bound : ∀ t ∈ I, ‖φ t‖ ≤ R)
    (h_dist : ∀ t ∈ I, δ ≤ infDist (φ t) Uᶜ) :
    ¬ BddAbove I := by
  intro hI
  have hEscape :=
    IsMaximalODESolution.norm_unbounded_or_dist_boundary_tendsto_zero_of_properSpace
      (h:=h) hI hf hU h_subset R δ hδ
  rcases (eventually_nhdsLT_iff (a:=sSup I)
    (p:=fun t => t ∈ I → (R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ))).1 hEscape with
    ⟨l, hl, hl_prop⟩
  rcases (lt_csSup_iff hI hI_nonempty).1 hl with ⟨t, htI, hlt⟩
  have ht_lt : t < sSup I := by
    have hnhds : I ∈ 𝓝 t := h.isOpen.mem_nhds htI
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hball⟩
    have ht' : t + ε / 2 ∈ I := by
      have hhalf_lt : ε / 2 < ε := by nlinarith [hεpos]
      have hdist_lt : dist (t + ε / 2) t < ε := by
        have h_abs : |ε| / 2 < ε := by
          simpa [abs_of_pos hεpos] using hhalf_lt
        simpa [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_abs
      exact hball hdist_lt
    have hlt' : t < t + ε / 2 := by nlinarith [hεpos]
    have ht'_le : t + ε / 2 ≤ sSup I := le_csSup hI ht'
    exact lt_of_lt_of_le hlt' ht'_le
  have hescape := hl_prop t ⟨hlt, ht_lt⟩ htI
  have hnot_norm : ¬ R < ‖φ t‖ := not_lt_of_ge (h_bound t htI)
  have hnot_dist : ¬ infDist (φ t) Uᶜ < δ := not_lt_of_ge (h_dist t htI)
  exact hescape.elim hnot_norm hnot_dist
