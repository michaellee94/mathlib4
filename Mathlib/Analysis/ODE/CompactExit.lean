/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
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

theorem IsIntegralCurveOn.comp_neg_iff :
    IsIntegralCurveOn (f ∘ Neg.neg) (fun t x ↦ - v (-t) x) (Neg.neg ⁻¹' I) ↔
    IsIntegralCurveOn f v I := by
  have hset : ((-1 : ℝ)⁻¹ • I) = (Neg.neg ⁻¹' I) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      refine ⟨-x, ?_, by simp⟩
      simpa using hx
  simpa [hset, Function.comp, mul_neg_one, Pi.smul_apply, neg_one_smul] using
    (isIntegralCurveOn_comp_mul_ne_zero (γ:=f) (v:=v) (s:=I) (a:=-1) (by norm_num)).symm

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
        (IsIntegralCurveOn.comp_neg_iff (v:=fun t x ↦ - v (-t) x) (f:=g) (I:=J)).mpr hg
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
**Right-endpoint compact-exit lemma (abstract extension form).**

Assume a maximal solution `(v, f, I)` has bounded right endpoint and that any time the trajectory
remains in a compact set near `sSup I`, we can build an extension past `sSup I`.
Then `(v, f, I)` must eventually leave every compact set as it approaches `sSup I` from the left.
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
  intro K hK ε hε
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
  rcases h_extend K hK ε hε hforall with ⟨g, J, hJ, hJopen, hJconn, hIJ, hEq, hsup⟩
  rcases hsup with ⟨t, htJ, ht_sup⟩
  have h_eq : I = J := h.is_maximal g J hJ hJopen hJconn hIJ hEq
  have ht_le : t ≤ sSup I := by
    have : t ∈ I := by simpa [h_eq] using htJ
    exact le_csSup hI this
  exact (not_lt_of_ge ht_le) ht_sup

/--
**Left-endpoint compact-exit lemma (abstract extension form).**

Assume a maximal solution `(v, f, I)` has bounded left endpoint and that any time the trajectory
remains in a compact set near `sInf I`, we can build an extension past `sInf I` to the left.
Then `(v, f, I)` must eventually leave every compact set as it approaches `sInf I` from the right.
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
  intro K hK ε hε
  have hne : I.Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty] at h_empty
    have h_cond : ∀ t ∈ I, t < sInf I + ε → f t ∈ K := by simp [h_empty]
    rcases h_extend K hK ε hε h_cond with ⟨g, J, hg, hJopen, hJconn, hIJ, hEq, ⟨t, htJ, ht_le⟩⟩
    have : I = J := h.is_maximal g J hg hJopen hJconn hIJ hEq
    rw [this.symm, h_empty] at htJ
    exact htJ
  have h_rev_bound : sSup (Neg.neg ⁻¹' I) = -sInf I := by
    apply sSup_preimage_neg hne hI
  rcases IsMaximalODESolution.leavesEveryCompact_right
    (IsMaximalODESolution.comp_neg_iff.mpr h) (BddAbove_preimage_neg hI)
    (by
      intro K' hK' ε' hε' htraj
      have htraj' : ∀ t ∈ I, t < sInf I + ε' → f t ∈ K' := by
        intro t htI ht
        have htI' : -t ∈ Neg.neg ⁻¹' I := by simpa
        have ht' : sSup (Neg.neg ⁻¹' I) - ε' < -t := by
          rw [h_rev_bound]
          linarith
        have hmem := htraj (-t) htI' ht'
        simpa [Function.comp] using hmem
      rcases h_extend K' hK' ε' hε' htraj' with ⟨g, J, hg, hJopen, hJconn, hIJ, hEq, hsup⟩
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
    ) K hK ε hε
    with ⟨t, htI, ht_sup, ht_less, ht_not⟩
  have htI' : -t ∈ I := by simpa using htI
  refine ⟨-t, htI', ?_, ?_, ?_⟩
  · rw [h_rev_bound] at ht_sup
    linarith
  · rw [h_rev_bound] at ht_less
    linarith
  · simpa [Function.comp] using ht_not

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
**Left-endpoint compact-exit lemma (autonomous, global $C^1$).**

If `f` is $C^1$ everywhere and globally Lipschitz, then a maximal solution to `x' = f x`
must leave every compact set as it approaches `sInf I` from the right.
-/
theorem IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddBelow I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (K_const : NNReal) (h_lip : LipschitzWith K_const f) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ φ t ∉ K := by
  have h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
    intro K hK
    rcases uniform_time_of_existence_autonomous_compact_global (f:=f) hf hK with ⟨ε, hε, H⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx t₀ ht₀
    exact H x hx t₀
  exact IsMaximalODESolution.leavesEveryCompact_left_autonomous
    (h:=h) hI hI_nonempty K hK h_uniform K_const h_lip

/--
**Right-endpoint compact-exit lemma (autonomous, global $C^1$).**

If `f` is $C^1$ everywhere and globally Lipschitz, then a maximal solution to `x' = f x`
must leave every compact set as it approaches `sSup I` from the left.
-/
theorem IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (K_const : NNReal) (h_lip : LipschitzWith K_const f) :
    ∀ ε : ℝ, ε > 0 → ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ φ t ∉ K := by
  have h_uniform : ∀ K : Set E, IsCompact K → ∃ ε : ℝ,
      ε > 0 ∧ ∀ x ∈ K, ∀ t₀ ∈ I, ∃ α : ℝ → E,
        α t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
    intro K hK
    rcases uniform_time_of_existence_autonomous_compact_global (f:=f) hf hK with ⟨ε, hε, H⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx t₀ ht₀
    exact H x hx t₀
  exact IsMaximalODESolution.leavesEveryCompact_right_autonomous
    (h:=h) hI hI_nonempty K hK h_uniform K_const h_lip

/--
**Global existence criterion (right-unbounded).**

If a maximal autonomous solution with a global $C^1$ vector field stays inside a compact set,
then its domain cannot be bounded above.
-/
theorem IsMaximalODESolution.not_bddAbove_of_compact_bound_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (K_const : NNReal) (h_lip : LipschitzWith K_const f)
    (htraj : ∀ t ∈ I, φ t ∈ K) :
    ¬ BddAbove I := by
  intro hI
  rcases (IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty K hK hf K_const h_lip) 1 (by norm_num)
    with ⟨t, htI, _, _, ht_not⟩
  exact ht_not (htraj t htI)

/--
**Global existence criterion (left-unbounded).**

If a maximal autonomous solution with a global $C^1$ vector field stays inside a compact set,
then its domain cannot be bounded below.
-/
theorem IsMaximalODESolution.not_bddBelow_of_compact_bound_autonomous_of_contDiffAt
    [CompleteSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI_nonempty : I.Nonempty)
    (K : Set E) (hK : IsCompact K) (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (K_const : NNReal) (h_lip : LipschitzWith K_const f)
    (htraj : ∀ t ∈ I, φ t ∈ K) :
    ¬ BddBelow I := by
  intro hI
  rcases (IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty K hK hf K_const h_lip) 1 (by norm_num)
    with ⟨t, htI, _, _, ht_not⟩
  exact ht_not (htraj t htI)

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
    (K_const : NNReal) (h_lip : LipschitzWith K_const f)
    (htraj : ∀ t ∈ I, φ t ∈ K) :
    ¬ BddAbove I ∧ ¬ BddBelow I := by
  refine ⟨?_, ?_⟩
  · exact IsMaximalODESolution.not_bddAbove_of_compact_bound_autonomous_of_contDiffAt
      (h:=h) hI_nonempty K hK hf K_const h_lip htraj
  · exact IsMaximalODESolution.not_bddBelow_of_compact_bound_autonomous_of_contDiffAt
      (h:=h) hI_nonempty K hK hf K_const h_lip htraj

/--
**Finite-time blow-up (right, proper spaces).**

If `E` is a proper space, then compact-exit implies that the norm becomes arbitrarily large
near a finite right endpoint.
-/
theorem IsMaximalODESolution.norm_unbounded_right_autonomous_of_contDiffAt
    [CompleteSpace E] [ProperSpace E]
    {f : E → E} {φ : ℝ → E} {I : Set ℝ}
    (h : IsMaximalODESolution (fun _ => f) φ I) (hI : BddAbove I) (hI_nonempty : I.Nonempty)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (K_const : NNReal) (h_lip : LipschitzWith K_const f) :
    ∀ R : ℝ, ∀ ε > 0, ∃ t ∈ I, sSup I - ε < t ∧ t < sSup I ∧ R < ‖φ t‖ := by
  intro R ε hε
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall _ _
  rcases (IsMaximalODESolution.leavesEveryCompact_right_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty (K:=closedBall (0 : E) R) hK hf K_const h_lip) ε hε
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
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x)
    (K_const : NNReal) (h_lip : LipschitzWith K_const f) :
    ∀ R : ℝ, ∀ ε > 0, ∃ t ∈ I, t < sInf I + ε ∧ sInf I < t ∧ R < ‖φ t‖ := by
  intro R ε hε
  have hK : IsCompact (closedBall (0 : E) R) := isCompact_closedBall _ _
  rcases (IsMaximalODESolution.leavesEveryCompact_left_autonomous_of_contDiffAt
    (h:=h) hI hI_nonempty (K:=closedBall (0 : E) R) hK hf K_const h_lip) ε hε
    with ⟨t, htI, ht_eps, ht_inf, ht_not⟩
  have hdist : R < dist (φ t) 0 := by
    have : ¬ dist (φ t) 0 ≤ R := by
      intro hle
      exact ht_not (by simpa [mem_closedBall] using hle)
    exact lt_of_not_ge this
  have hnorm : R < ‖φ t‖ := by
    simpa [dist_eq_norm] using hdist
  exact ⟨t, htI, ht_eps, ht_inf, hnorm⟩
