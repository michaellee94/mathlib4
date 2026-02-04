/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Algebra.Order.Group.Bounds
public import Mathlib.Analysis.ODE.MaximalSolution
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compact-exit lemma ("lemme des bouts")

This module provides formal versions of the compact-exit lemma for maximal ODE solutions.
A maximal solution must leave every compact set as it approaches the boundary of its domain.

The key results are:
- `IsMaximalODESolution.leavesEveryCompact_right_autonomous`: autonomous case with C¹ vector field
- `IsMaximalODESolution.leavesEveryCompact_left_autonomous`: autonomous left-endpoint analog
- `IsMaximalODESolution.leavesEveryCompact_right_time_dependent`: time-dependent case with uniform
  existence hypotheses
- `IsMaximalODESolution.leavesEveryCompact_right_time_dependent_of_IsPicardLindelof_on_Icc`:
  time-dependent case with Picard–Lindelöf hypotheses on a time strip
- `IsMaximalODESolution.unbounded_of_compact_bound_autonomous_of_contDiffAt`: global-existence
  criterion from a compact bound on the trajectory

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
**Right-endpoint compact-exit lemma (abstract extension form, with predicate on compacts).**

Assume a maximal solution `(v, f, I)` has bounded right endpoint and that, for every compact set
`K` satisfying `P`, if the trajectory remains in `K` near `sSup I`, we can build an extension past
`sSup I`.
Then `(v, f, I)` must eventually leave every compact set `K` satisfying `P` as it approaches
`sSup I` from the left.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_of_property
    {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v f I) (hI : BddAbove I)
    (P : Set E → Prop)
    (h_extend :
      ∀ K : Set E, IsCompact K → P K → ∀ ε > (0 : ℝ),
        (∀ t ∈ I, sSup I - ε < t → f t ∈ K) →
          ∃ g J,
            IsIntegralCurveOn g v J ∧ IsOpen J ∧ IsConnected J ∧
              I ⊆ J ∧ EqOn f g I ∧ ∃ t, t ∈ J ∧ sSup I < t) :
    ∀ K : Set E, IsCompact K → P K → ∀ ε > (0 : ℝ),
      ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ f t ∉ K := by
  intro K hK hP ε hε
  by_contra hcontra
  have hforall : ∀ t ∈ I, sSup I - ε < t → f t ∈ K := by
    intro t htI ht
    by_contra hnot
    have ht_lt : t < sSup I := by
      have hI_nonempty : I.Nonempty := ⟨t, htI⟩
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
      have hlt_witness : ∃ b ∈ I, t < b := by
        refine ⟨t + δ / 2, ht_in_I, ?_⟩
        nlinarith [hδpos]
      exact (lt_csSup_iff hI hI_nonempty).2 hlt_witness
    exact hcontra ⟨t, htI, ht, ht_lt, hnot⟩
  rcases h_extend K hK hP ε hε hforall with ⟨g, J, hJ, hJopen, hJconn, hIJ, hEq, hsup⟩
  rcases hsup with ⟨t, htJ, ht_sup⟩
  have h_eq : I = J := h.is_maximal g J hJ hJopen hJconn hIJ hEq
  have ht_le : t ≤ sSup I := by
    have : t ∈ I := by simpa [h_eq] using htJ
    exact le_csSup hI this
  exact (not_lt_of_ge ht_le) ht_sup

/--
**Right-endpoint compact-exit lemma (abstract extension form).**

This is a special case of `leavesEveryCompact_right_of_property` with `P := fun _ => True`.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right
    {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v f I) (hI : BddAbove I)
    (h_extend :
      ∀ K : Set E, IsCompact K → ∀ ε > (0 : ℝ),
        (∀ t ∈ I, sSup I - ε < t → f t ∈ K) →
          ∃ g J,
            IsIntegralCurveOn g v J ∧ IsOpen J ∧ IsConnected J ∧
              I ⊆ J ∧ EqOn f g I ∧ ∃ t, t ∈ J ∧ sSup I < t) :
    ∀ K : Set E, IsCompact K → ∀ ε > (0 : ℝ),
      ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ f t ∉ K := by
  simpa using
    (IsMaximalODESolution.leavesEveryCompact_right_of_property
      (h:=h) hI (P:=fun _ => True)
      (by
        intro K hK _ ε hε htraj
        exact h_extend K hK ε hε htraj))

/--
**Left-endpoint compact-exit lemma (abstract extension form, with predicate on compacts).**

Assume a maximal solution `(v, f, I)` has bounded left endpoint and that, for every compact set
`K` satisfying `P`, if the trajectory remains in `K` near `sInf I`, we can build an extension past
`sInf I` to the left.
Then `(v, f, I)` must eventually leave every compact set `K` satisfying `P` as it approaches
`sInf I` from the right.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_of_property
    {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v f I) (hI : BddBelow I)
    (P : Set E → Prop)
    (h_extend :
      ∀ K : Set E, IsCompact K → P K → ∀ ε > (0 : ℝ),
        (∀ t ∈ I, t < sInf I + ε → f t ∈ K) →
          ∃ g J,
            IsIntegralCurveOn g v J ∧ IsOpen J ∧ IsConnected J ∧
              I ⊆ J ∧ EqOn f g I ∧ ∃ t, t ∈ J ∧ t < sInf I) :
    ∀ K : Set E, IsCompact K → P K → ∀ ε > (0 : ℝ),
      ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ f t ∉ K := by
  intro K hK hP ε hε
  have hne : I.Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    have h_cond : ∀ t ∈ I, t < sInf I + ε → f t ∈ K := by simp [h_empty]
    rcases h_extend K hK hP ε hε h_cond with ⟨g, J, hg, hJopen, hJconn, hIJ, hEq, ⟨t, htJ, ht_le⟩⟩
    have : I = J := h.is_maximal g J hg hJopen hJconn hIJ hEq
    rw [this.symm, h_empty] at htJ
    exact htJ
  have h_rev_bound : sSup (Neg.neg ⁻¹' I) = -sInf I := by
    apply sSup_preimage_neg hne hI
  rcases IsMaximalODESolution.leavesEveryCompact_right_of_property
    (IsMaximalODESolution.comp_neg_iff.mpr h) (BddAbove_preimage_neg hI) P
    (by
      intro K' hK' hP' ε' hε' htraj
      have htraj' : ∀ t ∈ I, t < sInf I + ε' → f t ∈ K' := by
        intro t htI ht
        have htI' : -t ∈ Neg.neg ⁻¹' I := by simpa
        have ht' : sSup (Neg.neg ⁻¹' I) - ε' < -t := by
          rw [h_rev_bound]
          linarith
        have hmem := htraj (-t) htI' ht'
        simpa [Function.comp] using hmem
      rcases h_extend K' hK' hP' ε' hε' htraj' with ⟨g, J, hg, hJopen, hJconn, hIJ, hEq, hsup⟩
      rcases hsup with ⟨t, htJ, ht_inf⟩
      refine ⟨g ∘ Neg.neg, Neg.neg ⁻¹' J, IsIntegralCurveOn.comp_neg_iff.mpr hg,
              hJopen.preimage continuous_neg,
              (((Homeomorph.neg ℝ).isConnected_preimage (s:=J)).2 hJconn),
              preimage_mono hIJ,
              (fun t ht => by
                have ht' : -t ∈ I := by simpa using ht
                have hEq' : f (-t) = g (-t) := hEq (x:=-t) ht'
                simpa [Function.comp] using hEq'),
              ⟨-t, by simpa, by rw [h_rev_bound]; linarith⟩⟩
    ) K hK hP ε hε
    with ⟨t, htI, ht_sup, ht_less, ht_not⟩
  have htI' : -t ∈ I := by simpa using htI
  refine ⟨-t, htI', ?_, ?_, ?_⟩
  · rw [h_rev_bound] at ht_sup
    linarith
  · rw [h_rev_bound] at ht_less
    linarith
  · simpa [Function.comp] using ht_not

/--
**Left-endpoint compact-exit lemma (abstract extension form).**

This is a special case of `leavesEveryCompact_left_of_property` with `P := fun _ => True`.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left
    {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v f I) (hI : BddBelow I)
    (h_extend :
      ∀ K : Set E, IsCompact K → ∀ ε > (0 : ℝ),
        (∀ t ∈ I, t < sInf I + ε → f t ∈ K) →
          ∃ g J,
            IsIntegralCurveOn g v J ∧ IsOpen J ∧ IsConnected J ∧
              I ⊆ J ∧ EqOn f g I ∧ ∃ t, t ∈ J ∧ t < sInf I) :
    ∀ K : Set E, IsCompact K → ∀ ε > (0 : ℝ),
      ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ f t ∉ K := by
  simpa using
    (IsMaximalODESolution.leavesEveryCompact_left_of_property
      (h:=h) hI (P:=fun _ => True)
      (by
        intro K hK _ ε hε htraj
        exact h_extend K hK ε hε htraj))

/--
**Right-endpoint compact-exit lemma (open-domain localization).**

This is the compact-exit lemma restricted to compact sets contained in a given set `U`.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_subset
    {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ} {U : Set E}
    (h : IsMaximalODESolution v f I) (hI : BddAbove I)
    (h_extend :
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ ε > (0 : ℝ),
        (∀ t ∈ I, sSup I - ε < t → f t ∈ K) →
          ∃ g J,
            IsIntegralCurveOn g v J ∧ IsOpen J ∧ IsConnected J ∧
              I ⊆ J ∧ EqOn f g I ∧ ∃ t, t ∈ J ∧ sSup I < t) :
    ∀ K : Set E, IsCompact K → K ⊆ U → ∀ ε > (0 : ℝ),
      ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ f t ∉ K := by
  simpa using
    (IsMaximalODESolution.leavesEveryCompact_right_of_property
      (h:=h) hI (P:=fun K => K ⊆ U)
      (by
        intro K hK hKU ε hε htraj
        exact h_extend K hK hKU ε hε htraj))

/--
**Left-endpoint compact-exit lemma (open-domain localization).**

This is the compact-exit lemma restricted to compact sets contained in a given set `U`.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_subset
    {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ} {U : Set E}
    (h : IsMaximalODESolution v f I) (hI : BddBelow I)
    (h_extend :
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ ε > (0 : ℝ),
        (∀ t ∈ I, t < sInf I + ε → f t ∈ K) →
          ∃ g J,
            IsIntegralCurveOn g v J ∧ IsOpen J ∧ IsConnected J ∧
              I ⊆ J ∧ EqOn f g I ∧ ∃ t, t ∈ J ∧ t < sInf I) :
    ∀ K : Set E, IsCompact K → K ⊆ U → ∀ ε > (0 : ℝ),
      ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ f t ∉ K := by
  simpa using
    (IsMaximalODESolution.leavesEveryCompact_left_of_property
      (h:=h) hI (P:=fun K => K ⊆ U)
      (by
        intro K hK hKU ε hε htraj
        exact h_extend K hK hKU ε hε htraj))

/--
**Right-endpoint compact-exit lemma (time-dependent, uniform existence hypothesis).**

Assume a uniform existence window for all initial data in a compact set `K` (for initial times
in the domain `I`), and assume a global Lipschitz condition on `v t` uniformly in `t`.
Then a maximal solution to `x' = v t x` must leave every compact set as it approaches `sSup I`
from the left.

This is the concrete form of the right-endpoint lemma once uniform existence is available.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_time_dependent
    {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t)
    (K_const : NNReal) (h_lip : ∀ t : ℝ, LipschitzWith K_const (v t)) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ φ t ∉ K := by
  intro ε hε
  classical
  refine IsMaximalODESolution.leavesEveryCompact_right (h:=h) hI ?h_extend K hK ε hε
  intro K' hK' ε' hε' htraj
  rcases h_uniform K' hK' with ⟨ε₀, hε₀, H⟩
  have hδpos : (0 : ℝ) < min (ε' : ℝ) (ε₀ / 2) := lt_min hε' (half_pos hε₀)
  have hsup_lt : sSup I - min (ε' : ℝ) (ε₀ / 2) < sSup I := by
    exact sub_lt_self _ hδpos
  rcases (lt_csSup_iff hI hI_nonempty).1 hsup_lt with ⟨t, htI, htδ⟩
  have ht_eps' : sSup I - ε' < t := by
    have hmin_le : min (ε' : ℝ) (ε₀ / 2) ≤ ε' := min_le_left _ _
    have hsub_le : sSup I - ε' ≤ sSup I - min (ε' : ℝ) (ε₀ / 2) := by
      exact sub_le_sub_left hmin_le _
    exact lt_of_le_of_lt hsub_le htδ
  have ht_eps0 : sSup I - ε₀ / 2 < t := by
    have hmin_le : min (ε' : ℝ) (ε₀ / 2) ≤ ε₀ / 2 := min_le_right _ _
    have hsub_le : sSup I - ε₀ / 2 ≤ sSup I - min (ε' : ℝ) (ε₀ / 2) := by
      exact sub_le_sub_left hmin_le _
    exact lt_of_le_of_lt hsub_le htδ
  have htK : φ t ∈ K' := htraj t htI ht_eps'
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
  refine ⟨g, J, hJ_curve, hJ_open, hJ_conn, ?_, hEq, ?_⟩
  · exact subset_union_left
  · refine ⟨t + ε₀ / 2, ?_, ?_⟩
    · have : t + ε₀ / 2 ∈ Ioo (t - ε₀) (t + ε₀) := by
        constructor <;> nlinarith [hε₀]
      exact Or.inr this
    · nlinarith [ht_eps0]

/--
**Left-endpoint compact-exit lemma (time-dependent, uniform existence hypothesis).**

Assume a uniform existence window for all initial data in a compact set `K` (for initial times
in the domain `I`), and assume a global Lipschitz condition on `v t` uniformly in `t`.
Then a maximal solution to `x' = v t x` must leave every compact set as it approaches `sInf I`
from the right.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_time_dependent
    {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v t (α t)) t)
    (K_const : NNReal) (h_lip : ∀ t : ℝ, LipschitzWith K_const (v t)) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ φ t ∉ K := by
  intro ε hε
  let v_rev := fun t x ↦ - v (-t) x
  let f_rev := φ ∘ Neg.neg
  let I_rev := Neg.neg ⁻¹' I
  have h_rev : IsMaximalODESolution v_rev f_rev I_rev := IsMaximalODESolution.comp_neg_iff.mpr h
  have hI_rev_bdd : BddAbove I_rev := BddAbove_preimage_neg hI
  have hI_rev_nonempty : I_rev.Nonempty := by
    rcases hI_nonempty with ⟨t, ht⟩
    exact ⟨-t, by simpa [I_rev] using ht⟩
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
  rcases IsMaximalODESolution.leavesEveryCompact_right_time_dependent
     h_rev hI_rev_bdd hI_rev_nonempty K hK h_uniform' K_const h_lip' ε hε
     with ⟨t, htI, ht_sup, ht_less, ht_not⟩
  have htI' : -t ∈ I := by simpa using htI
  refine ⟨-t, htI', ?_, ?_, ?_⟩
  · rw [h_rev_bound] at ht_sup
    linarith
  · rw [h_rev_bound] at ht_less
    linarith
  · simpa [Function.comp] using ht_not

/--
**Right-endpoint compact-exit lemma (time-dependent, Picard–Lindelöf on a strip).**

Assume global Picard–Lindelöf hypotheses for `v` on a time strip `Icc tmin tmax`, and assume
`I ⊆ Icc tmin' tmax'` with `tmin < tmin'` and `tmax' < tmax`. Then a maximal solution must leave
every compact set as it approaches `sSup I` from the left.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_time_dependent_of_IsPicardLindelof_on_Icc
    [CompleteSpace E]
    {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    {tmin tmax tmin' tmax' : ℝ} (htmin : tmin < tmin') (htmax : tmax' < tmax)
    (hIcc : I ⊆ Icc tmin' tmax')
    (hpl : ∀ x : E, ∀ t₀ : Icc tmin tmax,
      ∃ a r L Kc : NNReal, IsPicardLindelof v (tmin:=tmin) (tmax:=tmax) t₀ x a r L Kc)
    (K : Set E) (hK : IsCompact K)
    (K_const : NNReal) (h_lip : ∀ t : ℝ, LipschitzWith K_const (v t)) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ φ t ∉ K := by
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
  exact IsMaximalODESolution.leavesEveryCompact_right_time_dependent
    (h:=h) hI hI_nonempty K hK h_uniform K_const h_lip

/--
**Left-endpoint compact-exit lemma (time-dependent, Picard–Lindelöf on a strip).**

Assume global Picard–Lindelöf hypotheses for `v` on a time strip `Icc tmin tmax`, and assume
`I ⊆ Icc tmin' tmax'` with `tmin < tmin'` and `tmax' < tmax`. Then a maximal solution must leave
every compact set as it approaches `sInf I` from the right.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_time_dependent_of_IsPicardLindelof_on_Icc
    [CompleteSpace E]
    {v : ℝ → E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution v φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    {tmin tmax tmin' tmax' : ℝ} (htmin : tmin < tmin') (htmax : tmax' < tmax)
    (hIcc : I ⊆ Icc tmin' tmax')
    (hpl : ∀ x : E, ∀ t₀ : Icc tmin tmax,
      ∃ a r L Kc : NNReal, IsPicardLindelof v (tmin:=tmin) (tmax:=tmax) t₀ x a r L Kc)
    (K : Set E) (hK : IsCompact K)
    (K_const : NNReal) (h_lip : ∀ t : ℝ, LipschitzWith K_const (v t)) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ φ t ∉ K := by
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
  exact IsMaximalODESolution.leavesEveryCompact_left_time_dependent
    (h:=h) hI hI_nonempty K hK h_uniform K_const h_lip

/--
**Right-endpoint compact-exit lemma (autonomous, uniform existence hypothesis).**

Assume a uniform existence window for all initial data in a compact set `K` (for initial times
in the domain `I`), and assume a global Lipschitz condition on `f`. Then a maximal solution to
`x' = f x` must leave every compact set as it approaches `sSup I` from the left.
-/
 theorem IsMaximalODESolution.leavesEveryCompact_right_autonomous
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t)
    (K_const : NNReal) (h_lip : LipschitzWith K_const f) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ φ t ∉ K := by
  refine IsMaximalODESolution.leavesEveryCompact_right_time_dependent
    (v:=fun _ => f) (h:=h) hI hI_nonempty K hK h_uniform K_const (fun _ => h_lip)

/--
**Left-endpoint compact-exit lemma (autonomous, uniform existence hypothesis).**

Assume a uniform existence window for all initial data in a compact set `K` (for initial times
in the domain `I`), and assume a global Lipschitz condition on `f`. Then a maximal solution to
`x' = f x` must leave every compact set as it approaches `sInf I` from the right.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_autonomous
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K)
    (h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t)
    (K_const : NNReal) (h_lip : LipschitzWith K_const f) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ φ t ∉ K := by
  refine IsMaximalODESolution.leavesEveryCompact_left_time_dependent
    (v:=fun _ => f) (h:=h) hI hI_nonempty K hK h_uniform K_const (fun _ => h_lip)

/--
**Right-endpoint compact-exit lemma (autonomous, global $C^1$).**

If `f` is $C^1$ everywhere, then a maximal solution to `x' = f x` must leave every compact set
as it approaches `sSup I` from the left.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ φ t ∉ K := by
  classical
  -- Step 0: From the pointwise `C^1` assumption, record that `f` is globally `C^1`.
  -- This is used only to invoke standard local-Lipschitz facts.
  have hf_contDiff : ContDiff ℝ 1 f := (contDiff_iff_contDiffAt.mpr hf)
  -- A globally `C^1` vector field is locally Lipschitz.
  have h_locLip : LocallyLipschitz f := ContDiff.locallyLipschitz hf_contDiff
  -- Step 1: Build the uniform time-of-existence input needed for the abstract compact-exit lemma.
  -- We use the global autonomous uniform existence theorem on each compact set.
  have h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
    intro K hK
    rcases uniform_time_of_existence_autonomous_compact_global (f:=f) hf hK with ⟨ε, hε, H⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx t₀ ht₀
    exact H x hx t₀
  intro ε hε
  -- Step 2: Apply the generic (time-dependent) right-endpoint compact-exit lemma.
  -- Its only nontrivial input is an “extendability contradiction” `h_extend`:
  -- if the trajectory stays in a compact set close enough to the endpoint, we can extend
  -- the solution past `sSup I`, contradicting maximality.
  refine IsMaximalODESolution.leavesEveryCompact_right (h:=h) hI ?h_extend K hK ε hε
  intro K' hK' ε' hε' htraj
  -- We assume the trajectory stays in a compact set `K'` on a terminal segment of the domain.
  -- From uniform existence on `K'`, pick a local solution `α` through the point `φ t`.
  rcases h_uniform K' hK' with ⟨ε₀, hε₀, H⟩
  -- Choose a time `t ∈ I` sufficiently close to `sSup I` but with room to fit in the local window.
  have hδpos : (0 : ℝ) < min (ε' : ℝ) (ε₀ / 2) := lt_min hε' (half_pos hε₀)
  have hsup_lt : sSup I - min (ε' : ℝ) (ε₀ / 2) < sSup I := by
    exact sub_lt_self _ hδpos
  rcases (lt_csSup_iff hI hI_nonempty).1 hsup_lt with ⟨t, htI, htδ⟩
  have ht_eps' : sSup I - ε' < t := by
    have hmin_le : min (ε' : ℝ) (ε₀ / 2) ≤ ε' := min_le_left _ _
    have hsub_le : sSup I - ε' ≤ sSup I - min (ε' : ℝ) (ε₀ / 2) := by
      exact sub_le_sub_left hmin_le _
    exact lt_of_le_of_lt hsub_le htδ
  have ht_eps0 : sSup I - ε₀ / 2 < t := by
    have hmin_le : min (ε' : ℝ) (ε₀ / 2) ≤ ε₀ / 2 := min_le_right _ _
    have hsub_le : sSup I - ε₀ / 2 ≤ sSup I - min (ε' : ℝ) (ε₀ / 2) := by
      exact sub_le_sub_left hmin_le _
    exact lt_of_le_of_lt hsub_le htδ
  have htK : φ t ∈ K' := htraj t htI ht_eps'
  rcases H (φ t) htK t htI with ⟨α, hαt, hα⟩
  -- `α` is an integral curve on the small interval `(t-ε₀, t+ε₀)`.
  have hα_curve : IsIntegralCurveOn α (fun _ => f) (Ioo (t - ε₀) (t + ε₀)) := by
    intro s hs
    exact (hα s hs).hasDerivWithinAt
  -- Step 3: Prove that `φ` and `α` agree on the overlap `I ∩ (t-ε₀, t+ε₀)`.
  -- This is the heart of the proof: we use *local* uniqueness (from local Lipschitzness)
  -- and a connectedness argument (“open-closed”) to upgrade pointwise agreement at `t`
  -- to agreement on the whole overlap.
  have h_eq_on : EqOn φ α (I ∩ Ioo (t - ε₀) (t + ε₀)) := by
    let K_int : Set ℝ := I ∩ Ioo (t - ε₀) (t + ε₀)
    have hK_open : IsOpen K_int := h.isOpen.inter isOpen_Ioo
    have htK_int : t ∈ K_int := by
      refine ⟨htI, ?_⟩
      constructor <;> linarith [hε₀]
    have hK_conn : IsConnected K_int := by
      have hI_ord : OrdConnected I := h.isConnected.isPreconnected.ordConnected
      have hIoo_ord : OrdConnected (Ioo (t - ε₀) (t + ε₀)) := ordConnected_Ioo
      have hK_ord : OrdConnected K_int := OrdConnected.inter hI_ord hIoo_ord
      exact ⟨⟨t, htK_int⟩, hK_ord.isPreconnected⟩
    -- Local uniqueness near a point `s` where `φ s = α s`:
    -- pick a neighborhood `U` where `f` is Lipschitz, and apply the standard ODE uniqueness lemma
    -- on a neighborhood of `s`.
    have hlocal : ∀ s ∈ K_int, φ s = α s → φ =ᶠ[𝓝 s] α := by
      intro s hs h_eq
      rcases h_locLip (φ s) with ⟨Kc, U, hU, hLipU⟩
      have hLip : ∀ᶠ t in 𝓝 s, LipschitzOnWith Kc (fun x => f x) U :=
        Filter.Eventually.of_forall (fun _ => hLipU)
      have hφ_cont : ContinuousAt φ s := by
        have hderiv := (h.deriv s hs.1).hasDerivAt (h.isOpen.mem_nhds hs.1)
        exact hderiv.continuousAt
      have hα_cont : ContinuousAt α s := (hα s hs.2).continuousAt
      have hφ_mem : ∀ᶠ t in 𝓝 s, φ t ∈ U := hφ_cont.preimage_mem_nhds hU
      have hα_mem : ∀ᶠ t in 𝓝 s, α t ∈ U := by
        have hU' : U ∈ 𝓝 (α s) := by simpa [h_eq] using hU
        exact hα_cont.preimage_mem_nhds hU'
      have hI_mem : ∀ᶠ t in 𝓝 s, t ∈ I := h.isOpen.mem_nhds hs.1
      have hIoo_mem : ∀ᶠ u in 𝓝 s, u ∈ Ioo (t - ε₀) (t + ε₀) :=
        isOpen_Ioo.mem_nhds hs.2
      have hφ_deriv : ∀ᶠ u in 𝓝 s, HasDerivAt φ (f (φ u)) u := by
        refine hI_mem.mono ?_
        intro u huI
        exact (h.deriv u huI).hasDerivAt (h.isOpen.mem_nhds huI)
      have hα_deriv : ∀ᶠ u in 𝓝 s, HasDerivAt α (f (α u)) u := by
        refine hIoo_mem.mono ?_
        intro u huIoo
        exact hα u huIoo
      have hφ_ev : ∀ᶠ u in 𝓝 s, HasDerivAt φ (f (φ u)) u ∧ φ u ∈ U :=
        hφ_deriv.and hφ_mem
      have hα_ev : ∀ᶠ u in 𝓝 s, HasDerivAt α (f (α u)) u ∧ α u ∈ U :=
        hα_deriv.and hα_mem
      exact ODE_solution_unique_of_eventually (v:=fun _ => f) (s:=fun _ => U) hLip hφ_ev hα_ev
        (by simp [h_eq])
    -- Define the “agreement set” inside the overlap.
    -- We show it is open (by local uniqueness), and closed relative to `K_int` (by continuity).
    -- Since `K_int` is connected and the agreement set is nonempty (it contains `t`),
    -- it must be all of `K_int`.
    let S : Set ℝ := {s | s ∈ K_int ∧ φ s = α s}
    have hS_open : IsOpen S := by
      refine isOpen_iff_mem_nhds.2 ?_
      intro s hs
      have hEq_ev : φ =ᶠ[𝓝 s] α := hlocal s hs.1 hs.2
      have hK_nhds : ∀ᶠ t in 𝓝 s, t ∈ K_int := hK_open.mem_nhds hs.1
      have hS_nhds : S ∈ 𝓝 s := by
        refine (hK_nhds.and hEq_ev).mono ?_
        rintro t ⟨htK, htEq⟩
        exact ⟨htK, htEq⟩
      exact hS_nhds
    -- Closedness of S inside K_int
    have hφ_cont_on : ContinuousOn φ K_int := h.deriv.continuousOn.mono (by intro _ hx; exact hx.1)
    have hα_cont_on : ContinuousOn α K_int := hα_curve.continuousOn.mono (by intro _ hx; exact hx.2)
    have hS_closure : closure S ∩ K_int ⊆ S := by
      intro x hx
      rcases hx with ⟨hx_cl, hxK⟩
      let S' : Set {t // t ∈ K_int} := {t | φ t = α t}
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
      have hS'closed : IsClosed S' := by
        simpa [S'] using isClosed_eq hcontφ hcontα
      have hx' : (⟨x, hxK⟩ : {t // t ∈ K_int}) ∈ closure S' := by
        have : x ∈ closure ((Subtype.val) '' S') := by
          simpa [hS_eq] using hx_cl
        exact (closure_subtype (x:=⟨x, hxK⟩) (s:=S')).2 this
      have hxS' : (⟨x, hxK⟩ : {t // t ∈ K_int}) ∈ S' := hS'closed.closure_subset hx'
      exact ⟨hxK, hxS'⟩
    have hK_preconn : IsPreconnected K_int := hK_conn.isPreconnected
    have hS_nonempty : (K_int ∩ S).Nonempty := by
      refine ⟨t, htK_int, ?_⟩
      exact ⟨htK_int, by simp [hαt]⟩
    have hsubset : K_int ⊆ S :=
      hK_preconn.subset_of_closure_inter_subset hS_open hS_nonempty hS_closure
    intro s hs
    exact (hsubset hs).2
  -- Step 4: Glue `φ` and the local solution `α` into a single integral curve
  -- `g` on a larger set `J`.
  -- On `I` we keep the original maximal solution.
  -- Outside `I` (but within the local window) we switch to `α`.
  let J : Set ℝ := I ∪ Ioo (t - ε₀) (t + ε₀)
  let g : ℝ → E := fun s => if s ∈ I then φ s else α s
  have hJ_open : IsOpen J := h.isOpen.union isOpen_Ioo
  have hJ_conn : IsConnected J := by
    have h_inter_nonempty : (I ∩ Ioo (t - ε₀) (t + ε₀)).Nonempty := by
      exact ⟨t, htI, by constructor <;> linarith [hε₀]⟩
    exact IsConnected.union h_inter_nonempty h.isConnected (isConnected_Ioo (by linarith [hε₀]))
  -- Show that the glued function `g` is still an integral curve on `J`.
  -- This is by cases:
  -- * if `s ∈ I`, then `g` agrees with `φ` near `s`.
  -- * otherwise `s` lies in the local window and `g` agrees with `α` near `s`.
  --   On the overlap, use `h_eq_on` to handle switching.
  have hJ_curve : IsIntegralCurveOn g (fun _ => f) J := by
    intro s hs
    by_cases hsI : s ∈ I
    · have hφ_deriv : HasDerivAt φ (f (φ s)) s :=
        (h.deriv s hsI).hasDerivAt (h.isOpen.mem_nhds hsI)
      have h_eq : g =ᶠ[𝓝 s] φ := by
        filter_upwards [h.isOpen.mem_nhds hsI] with y hyI
        simp [g, hyI]
      have h' : HasDerivAt g (f (g s)) s := by
        have h' := HasDerivAt.congr_of_eventuallyEq hφ_deriv h_eq
        simpa [g, hsI] using h'
      exact h'.hasDerivWithinAt
    · have hsIoo : s ∈ Ioo (t - ε₀) (t + ε₀) := hs.resolve_left hsI
      have hα_deriv : HasDerivAt α (f (α s)) s := hα s hsIoo
      have h_eq : g =ᶠ[𝓝 s] α := by
        have hIoo_nhds : Ioo (t - ε₀) (t + ε₀) ∈ 𝓝 s :=
          isOpen_Ioo.mem_nhds hsIoo
        filter_upwards [hIoo_nhds] with y hyIoo
        by_cases hyI : y ∈ I
        · have : y ∈ I ∩ Ioo (t - ε₀) (t + ε₀) := ⟨hyI, hyIoo⟩
          have h_eq_on' := h_eq_on this
          simp [g, hyI, h_eq_on']
        · simp [g, hyI]
      have h' : HasDerivAt g (f (g s)) s := by
        have h' := HasDerivAt.congr_of_eventuallyEq hα_deriv h_eq
        simpa [g, hsI] using h'
      exact h'.hasDerivWithinAt
  have hEq : EqOn φ g I := by
    intro s hsI
    simp [g, hsI]
  -- Step 5: This glued curve extends `φ` past `sSup I`.
  -- Use the point `t + ε₀/2`.
  -- This contradicts maximality.
  -- This is exactly what `leavesEveryCompact_right` needs from `h_extend`.
  refine ⟨g, J, hJ_curve, hJ_open, hJ_conn, ?_, hEq, ?_⟩
  · exact subset_union_left
  · refine ⟨t + ε₀ / 2, ?_, ?_⟩
    · have : t + ε₀ / 2 ∈ Ioo (t - ε₀) (t + ε₀) := by
        constructor <;> linarith [hε₀]
      exact Or.inr this
    · nlinarith [ht_eps0]

/--
**Left-endpoint compact-exit lemma (autonomous, global $C^1$).**

If `f` is $C^1$ everywhere, then a maximal solution to `x' = f x` must leave every compact set
as it approaches `sInf I` from the right.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ φ t ∉ K := by
  intro ε hε
  let v_rev : ℝ → E → E := fun _ x ↦ - f x
  let φ_rev : ℝ → E := φ ∘ Neg.neg
  let I_rev : Set ℝ := Neg.neg ⁻¹' I
  have h_rev : IsMaximalODESolution v_rev φ_rev I_rev := IsMaximalODESolution.comp_neg_iff.mpr h
  have hI_rev_bdd : BddAbove I_rev := BddAbove_preimage_neg hI
  have hI_rev_nonempty : I_rev.Nonempty := by
    rcases hI_nonempty with ⟨t, ht⟩
    exact ⟨-t, by simpa [I_rev] using ht⟩
  have h_rev_bound : sSup I_rev = -sInf I := by
    apply sSup_preimage_neg hI_nonempty hI
  have hf_rev : ∀ x : E, ContDiffAt ℝ 1 (fun x => - f x) x := by
    intro x
    simpa using (hf x).neg
  rcases (IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    (h:=h_rev) hI_rev_bdd hI_rev_nonempty K hK hf_rev) ε hε
    with ⟨t, htI, ht_sup, ht_less, ht_not⟩
  have htI' : -t ∈ I := by simpa [I_rev] using htI
  refine ⟨-t, htI', ?_, ?_, ?_⟩
  · rw [h_rev_bound] at ht_sup
    linarith
  · rw [h_rev_bound] at ht_less
    linarith
  · simpa [Function.comp, φ_rev] using ht_not

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
    rcases (IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
      (h:=h) hI hI_nonempty K hK hf) 1 (by norm_num)
      with ⟨t, htI, _, _, ht_not⟩
    exact ht_not (htraj t htI)
  · intro hI
    rcases (IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
      (h:=h) hI hI_nonempty K hK hf) 1 (by norm_num)
      with ⟨t, htI, _, _, ht_not⟩
    exact ht_not (htraj t htI)

/--
**Finite-time blow-up (right, proper spaces).**

If `E` is a proper space, then compact-exit implies that the norm becomes arbitrarily large
near a finite right endpoint.
-/
theorem IsMaximalODESolution.norm_unbounded_right_autonomous_of_contDiffAt
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∀ R : ℝ, ∀ ε > 0, ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ R < ‖φ t‖ := by
  intro R ε hε
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall _ _
  rcases (IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty (K:=closedBall (0 : E) R) hK hf) ε hε
    with ⟨t, htI, ht_eps, ht_sup, ht_not⟩
  have hdist : R < dist (φ t) 0 := by
    have : ¬ dist (φ t) 0 ≤ R := by
      intro hle
      exact ht_not (by simpa [mem_closedBall] using hle)
    exact lt_of_not_ge this
  have hnorm : R < ‖φ t‖ := by
    simpa [dist_eq_norm] using hdist
  exact ⟨t, htI, ht_eps, ht_sup, hnorm⟩

/--
**Finite-time blow-up (left, proper spaces).**

If `E` is a proper space, then compact-exit implies that the norm becomes arbitrarily large
near a finite left endpoint.
-/
theorem IsMaximalODESolution.norm_unbounded_left_autonomous_of_contDiffAt
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∀ R : ℝ, ∀ ε > 0, ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ R < ‖φ t‖ := by
  intro R ε hε
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall _ _
  rcases (IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty (K:=closedBall (0 : E) R) hK hf) ε hε
    with ⟨t, htI, ht_eps, ht_inf, ht_not⟩
  have hdist : R < dist (φ t) 0 := by
    have : ¬ dist (φ t) 0 ≤ R := by
      intro hle
      exact ht_not (by simpa [mem_closedBall] using hle)
    exact lt_of_not_ge this
  have hnorm : R < ‖φ t‖ := by
    simpa [dist_eq_norm] using hdist
  exact ⟨t, htI, ht_eps, ht_inf, hnorm⟩

/--
**Escape lemma (proper spaces).**

Let `U` be an open set and assume a maximal solution stays in `U`.
Near a finite right endpoint, the solution must either:
* escape every fixed norm bound, or
* get within any prescribed distance of `Uᶜ`.

Formally, for any `R` and any `δ > 0`, and any right-endpoint window `ε > 0`, there is
`t ∈ I` with `sSup I - ε < t < sSup I` such that
`R < ‖φ t‖` or `infDist (φ t) Uᶜ < δ`.
-/
theorem IsMaximalODESolution.norm_unbounded_or_dist_boundary_tendsto_zero_of_properSpace
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ} {U : Set E}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (hU : IsOpen U) (h_subset : ∀ t ∈ I, φ t ∈ U) :
    ∀ R : ℝ, ∀ δ > 0, ∀ ε > 0, ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧
      (R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ) := by
  classical
  intro R δ hδ ε hε
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
  rcases (IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty (K:=K) hK_compact hf) ε hε
    with ⟨t, htI, ht_eps, ht_sup, ht_not⟩
  refine ⟨t, htI, ht_eps, ht_sup, ?_⟩
  have h_in_U : φ t ∈ U := h_subset t htI
  have ht_not' : ¬ (‖φ t‖ ≤ R ∧ δ ≤ infDist (φ t) Uᶜ) := by
    intro hKcond
    exact ht_not ⟨h_in_U, hKcond.1, hKcond.2⟩
  have ht_disj : R < ‖φ t‖ ∨ infDist (φ t) Uᶜ < δ := by
    have ht_or : ¬ (‖φ t‖ ≤ R) ∨ ¬ (δ ≤ infDist (φ t) Uᶜ) :=
      not_and_or.mp ht_not'
    exact ht_or.elim (fun h => Or.inl (lt_of_not_ge h)) (fun h => Or.inr (lt_of_not_ge h))
  exact ht_disj
