/-
Copyright (c) 2026 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Existence and uniqueness of integral curves in normed spaces

This file states the results of Gronwall's inequality and the Picard-Lindelöf theorem in terms
of the integral curve API (`IsIntegralCurve`, `IsIntegralCurveOn`, `IsIntegralCurveAt`).

## Main results

## Tags

integral curve, vector field, existence, uniqueness, Picard-Lindelöf, Gronwall
-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

/-! ## Existence of solutions to ODEs -/

namespace IsPicardLindelof

open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local solution whose initial point `x` may be different from the centre `x₀` of
the closed ball within which the properties of the vector field hold. -/
theorem exists_eq_isIntegralCurveOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ IsIntegralCurveOn α f (Icc tmin tmax) := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀], fun t ht ↦ ?_⟩
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. -/
theorem exists_eq_isIntegralCurveOn₀
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurveOn α f (Icc tmin tmax) :=
  exists_eq_isIntegralCurveOn hf (mem_closedBall_self le_rfl)

open Classical in
/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is Lipschitz continuous in the initial point. -/
theorem exists_forall_mem_closedBall_eq_isIntegralCurveOn_lipschitzOnWith
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      IsIntegralCurveOn (α x) f (Icc tmin tmax)) ∧
      ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  have (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  refine ⟨α', fun x hx ↦ ⟨?_, fun t ht ↦ ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dif_pos hx, FunSpace.compProj_apply]
    apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
      x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  · obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp_rw [hα']
    rw [dif_pos hx, dif_pos hy, FunSpace.compProj_apply, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow and that it is continuous on its domain as a (partial) map `E × ℝ → E`. -/
theorem exists_forall_mem_closedBall_eq_isIntegralCurveOn_continuousOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E × ℝ → E, (∀ x ∈ closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      IsIntegralCurveOn (α ⟨x, ·⟩) f (Icc tmin tmax)) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  obtain ⟨α, hα1, L', hα2⟩ := hf.exists_forall_mem_closedBall_eq_isIntegralCurveOn_lipschitzOnWith
  refine ⟨uncurry α, hα1, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hα2
  exact fun x hx ↦ (hα1 x hx).2.continuousOn

/-- **Picard-Lindelöf (Cauchy-Lipschitz) theorem**, differential form. This version shows the
existence of a local flow. -/
theorem exists_forall_mem_closedBall_eq_isIntegralCurveOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      IsIntegralCurveOn (α x) f (Icc tmin tmax) :=
  have ⟨α, hα⟩ := exists_forall_mem_closedBall_eq_isIntegralCurveOn_lipschitzOnWith hf
  ⟨α, hα.1⟩

end IsPicardLindelof

/-! ## $C^1$ vector field -/

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {x₀ : E}

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x`, where
`x` may be different from `x₀`. -/
theorem exists_forall_mem_closedBall_exists_eq_isIntegralCurveOn
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      IsIntegralCurveOn α (fun _ ↦ f) (Ioo (t₀ - ε) (t₀ + ε)) := by
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf t₀
  refine ⟨r, hr, ε, hε, fun x hx ↦ ?_⟩
  have ⟨α, hα1, hα2⟩ := hpl.exists_eq_isIntegralCurveOn hx
  exact ⟨α, hα1, hα2.mono Ioo_subset_Icc_self⟩

/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits an
integral curve `α : ℝ → E` defined on an open interval, with initial condition `α t₀ = x₀`. -/
theorem exists_eq_isIntegralCurveAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurveAt α (fun _ ↦ f) t₀ := by
  have ⟨_, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_isIntegralCurveOn hf t₀
  have ⟨α, hα1, hα2⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  exact ⟨α, hα1, hα2.isIntegralCurveAt (Ioo_mem_nhds (by linarith) (by linarith))⟩

open Classical in
/-- If a vector field `f : E → E` is continuously differentiable at `x₀ : E`, then it admits a flow
`α : E → ℝ → E` defined on an open domain, with initial condition `α x t₀ = x` for all `x` within
the domain. -/
theorem exists_eventually_isIntegralCurveAt
    (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ α : E → ℝ → E, ∀ᶠ x in 𝓝 x₀,
      α x t₀ = x ∧ IsIntegralCurveAt (α x) (fun _ ↦ f) t₀ := by
  obtain ⟨r, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_isIntegralCurveOn hf t₀
  choose α hα using H
  refine ⟨fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then α x hx else 0, ?_⟩
  filter_upwards [closedBall_mem_nhds x₀ hr] with x hx
  simp only [dif_pos hx]
  exact ⟨(hα x hx).1,
    (hα x hx).2.isIntegralCurveAt (Ioo_mem_nhds (by linarith) (by linarith))⟩

end ContDiffAt
