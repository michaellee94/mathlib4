/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Orientation

/-!
# Manifold orientation helpers

This file defines an orientation-preserving structure groupoid on a model with corners.

## Main definitions

* `Manifold.modelSet`: the model-space set `I.symm ⁻¹' s ∩ range I`.
* `Manifold.jacobianDetWithin`: Jacobian determinant of a map in model coordinates.
* `Manifold.OrientationPreservingOn`: chart-space orientation-preserving condition on a set,
  using positive Jacobian determinant.
* `Manifold.orientationPreservingPregroupoid`: corresponding pregroupoid.
* `Manifold.orientationPreservingGroupoid`: corresponding structure groupoid.
* `Manifold.Orientable`: manifold-level orientability predicate.
* `Manifold.tangentOrientation`: a choice of orientation on each tangent space induced from the
  model fiber orientation.
-/

@[expose] public section

noncomputable section

open scoped Manifold
open Set

namespace Manifold

section Groupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- The model-space set corresponding to a set in chart space. -/
abbrev modelSet (s : Set H) : Set E := I.symm ⁻¹' s ∩ range I

/-- Jacobian determinant of `f` within `s` at `x`: the determinant of the Fréchet derivative
of `f` restricted to `s`, viewed as a linear map `E →ₗ[ℝ] E`. -/
def jacobianDetWithin (f : E → E) (s : Set E) (x : E) : ℝ :=
  LinearMap.det (↑(fderivWithin ℝ f s x) : E →ₗ[ℝ] E)

/-- Chart-level orientation-preserving condition on a set:
`C¹` in model coordinates with positive Jacobian determinant at every point. -/
def OrientationPreservingOn (f : H → H) (s : Set H) : Prop :=
  ContDiffOn ℝ 1 (I ∘ f ∘ I.symm) (modelSet I s) ∧ ∀ x ∈ modelSet I s,
    0 < jacobianDetWithin (I ∘ f ∘ I.symm) (modelSet I s) x

omit [FiniteDimensional ℝ E] in
theorem modelSet_uniqueDiffOn {s : Set H} (hs : IsOpen s) : UniqueDiffOn ℝ (modelSet I s) := by
  simpa [modelSet] using I.uniqueDiffOn_preimage hs

omit [FiniteDimensional ℝ E] in
theorem modelSet_inter (s t : Set H) : modelSet I (s ∩ t) = modelSet I s ∩ I.symm ⁻¹' t := by
  ext x
  simp [modelSet, and_left_comm, and_assoc, and_comm]

omit [FiniteDimensional ℝ E] in
theorem orientationPreservingOn_ofSet {s : Set H} (hs : IsOpen s) :
    OrientationPreservingOn I (OpenPartialHomeomorph.ofSet s hs) s := by
  refine ⟨?_, ?_⟩
  · have hIdOnModel : ContDiffOn ℝ 1 (fun x : E ↦ x) (modelSet I s) :=
      contDiff_id.contDiffOn.mono (subset_univ _)
    have hIIsymm : ContDiffOn ℝ 1 (I ∘ I.symm) (modelSet I s) := by
      refine hIdOnModel.congr ?_
      intro x hx
      exact I.right_inv hx.2
    refine hIIsymm.congr ?_
    intro x hx
    simp [Function.comp]
  · intro x hx
    have hEqOn : EqOn (I ∘ (OpenPartialHomeomorph.ofSet s hs : H → H) ∘ I.symm)
        (I ∘ I.symm) (modelSet I s) := by
      intro y hy
      simp [Function.comp]
    have hEqOnId : EqOn (I ∘ I.symm) (fun y : E ↦ y) (modelSet I s) := by
      intro y hy
      exact I.right_inv hy.2
    rw [jacobianDetWithin]
    rw [fderivWithin_congr hEqOn (hEqOn hx)]
    rw [fderivWithin_congr hEqOnId (hEqOnId hx)]
    rw [fderivWithin_id' ((modelSet_uniqueDiffOn I hs) x hx)]
    simp

/-- Pregroupoid of orientation-preserving chart maps. -/
def orientationPreservingPregroupoid : Pregroupoid H where
  property f s := OrientationPreservingOn I f s
  comp {f g u v} hf hg hu hv huv := by
    rcases hf with ⟨hfcont, hfdet⟩
    rcases hg with ⟨hgcont, hgdet⟩
    refine ⟨?_, ?_⟩
    · have hcompCont : ContDiffOn ℝ 1 (((I ∘ g ∘ I.symm) ∘ (I ∘ f ∘ I.symm)))
          (modelSet I (u ∩ f ⁻¹' v)) := by
        refine hgcont.comp (hfcont.mono ?_) ?_
        · intro x hx
          exact ⟨hx.1.1, hx.2⟩
        · intro x hx
          refine ⟨?_, Set.mem_range_self _⟩
          simpa [modelSet, Function.comp, I.left_inv] using hx.1.2
      have hfun : I ∘ (g ∘ f) ∘ I.symm = ((I ∘ g ∘ I.symm) ∘ (I ∘ f ∘ I.symm)) := by
        funext y
        simp [Function.comp, I.left_inv]
      simpa [hfun] using hcompCont
    · intro x hx
      let A : Set E := modelSet I (u ∩ f ⁻¹' v)
      let B : Set E := modelSet I v
      have hxB : (I ∘ f ∘ I.symm) x ∈ B := by
        refine ⟨?_, Set.mem_range_self _⟩
        simpa [A, B, modelSet, Function.comp, I.left_inv] using hx.1.2
      have hmaps : MapsTo (I ∘ f ∘ I.symm) A B := by
        intro y hy
        refine ⟨?_, Set.mem_range_self _⟩
        simpa [A, B, modelSet, Function.comp, I.left_inv] using hy.1.2
      have hfd : DifferentiableWithinAt ℝ (I ∘ f ∘ I.symm) A x :=
        (hfcont.differentiableOn (by decide) x (show x ∈ modelSet I u from ⟨hx.1.1, hx.2⟩)).mono
          (show A ⊆ modelSet I u from fun y hy => ⟨hy.1.1, hy.2⟩)
      have hgd : DifferentiableWithinAt ℝ (I ∘ g ∘ I.symm) B ((I ∘ f ∘ I.symm) x) :=
        (hgcont.differentiableOn (by decide) ((I ∘ f ∘ I.symm) x)
          (show (I ∘ f ∘ I.symm) x ∈ modelSet I v from hxB))
      have hcomp :
          fderivWithin ℝ (I ∘ (g ∘ f) ∘ I.symm) A x =
            (fderivWithin ℝ (I ∘ g ∘ I.symm) B ((I ∘ f ∘ I.symm) x)).comp
              (fderivWithin ℝ (I ∘ f ∘ I.symm) A x) := by
        have hfun : I ∘ (g ∘ f) ∘ I.symm = ((I ∘ g ∘ I.symm) ∘ (I ∘ f ∘ I.symm)) := by
          funext y
          simp [Function.comp, I.left_inv]
        rw [hfun]
        exact fderivWithin_comp x hgd hfd hmaps ((modelSet_uniqueDiffOn I huv) x hx)
      have hA_nhds : A ∈ nhdsWithin x (modelSet I u) := by
        refine mem_nhdsWithin.mpr ?_
        refine ⟨I.symm ⁻¹' (u ∩ f ⁻¹' v), huv.preimage I.continuous_symm, ?_, ?_⟩
        · simpa [A, modelSet, I.left_inv] using hx.1
        · intro y hy
          exact ⟨hy.1, hy.2.2⟩
      have hUniqueU : UniqueDiffWithinAt ℝ (modelSet I u) x :=
        (modelSet_uniqueDiffOn I hu) x ⟨hx.1.1, hx.2⟩
      have hderiv_f : fderivWithin ℝ (I ∘ f ∘ I.symm) (modelSet I u) x =
          fderivWithin ℝ (I ∘ f ∘ I.symm) A x :=
        fderivWithin_of_mem_nhdsWithin hA_nhds hUniqueU hfd
      have hdet_f : 0 < jacobianDetWithin (I ∘ f ∘ I.symm) A x := by
        simpa [jacobianDetWithin, hderiv_f] using
          (hfdet x (show x ∈ modelSet I u from ⟨hx.1.1, hx.2⟩))
      have hdet_g : 0 < jacobianDetWithin (I ∘ g ∘ I.symm) B ((I ∘ f ∘ I.symm) x) :=
        hgdet ((I ∘ f ∘ I.symm) x) (show (I ∘ f ∘ I.symm) x ∈ modelSet I v from hxB)
      rw [jacobianDetWithin, hcomp]
      rw [show
        LinearMap.det
            (↑((fderivWithin ℝ (I ∘ g ∘ I.symm) B ((I ∘ f ∘ I.symm) x)).comp
              (fderivWithin ℝ (I ∘ f ∘ I.symm) A x)) : E →ₗ[ℝ] E) =
          LinearMap.det
            ((↑(fderivWithin ℝ (I ∘ g ∘ I.symm) B ((I ∘ f ∘ I.symm) x)) : E →ₗ[ℝ] E) ∘ₗ
              (↑(fderivWithin ℝ (I ∘ f ∘ I.symm) A x) : E →ₗ[ℝ] E)) by simp]
      rw [LinearMap.det_comp]
      exact mul_pos hdet_g hdet_f
  id_mem := by
    refine ⟨?_, ?_⟩
    · have hIdOnModel : ContDiffOn ℝ 1 (fun x : E ↦ x) (modelSet I univ) := by
        exact contDiff_id.contDiffOn.mono (subset_univ _)
      refine hIdOnModel.congr ?_
      intro x hx
      simp [Function.comp, I.right_inv hx.2]
    · intro x hx
      have hEqOn : EqOn (I ∘ (id : H → H) ∘ I.symm) (fun y : E ↦ y) (modelSet I univ) := by
        intro y hy
        simp [Function.comp, I.right_inv hy.2]
      have hUnique : UniqueDiffWithinAt ℝ (modelSet I univ) x :=
        (modelSet_uniqueDiffOn I isOpen_univ) x hx
      have hderiv :
          fderivWithin ℝ (I ∘ (id : H → H) ∘ I.symm) (modelSet I univ) x =
            ContinuousLinearMap.id ℝ E := by
        calc
          fderivWithin ℝ (I ∘ (id : H → H) ∘ I.symm) (modelSet I univ) x =
              fderivWithin ℝ (fun y : E ↦ y) (modelSet I univ) x :=
            fderivWithin_congr hEqOn (hEqOn hx)
          _ = ContinuousLinearMap.id ℝ E := fderivWithin_id' hUnique
      rw [jacobianDetWithin, hderiv]
      simp
  locality {f u} hu h := by
    refine ⟨?_, ?_⟩
    · apply contDiffOn_of_locally_contDiffOn
      intro y hy
      rcases mem_range.1 hy.2 with ⟨x, rfl⟩
      have hxu : x ∈ u := by simpa [modelSet, I.left_inv] using hy.1
      rcases h x hxu with ⟨v, hv_open, hxv, hv⟩
      rcases hv with ⟨hvcont, _⟩
      have hs : modelSet I (u ∩ v) = modelSet I u ∩ I.symm ⁻¹' v := by
        simp [modelSet, preimage_inter, inter_assoc, inter_left_comm, inter_comm]
      rw [hs] at hvcont
      exact ⟨I.symm ⁻¹' v, hv_open.preimage I.continuous_symm, by simpa [I.left_inv] using hxv,
        hvcont⟩
    · intro y hy
      rcases h (I.symm y) hy.1 with ⟨v, hv_open, hyv, hv⟩
      rcases hv with ⟨hvcont, hvdet⟩
      have hyuv : y ∈ modelSet I (u ∩ v) := ⟨⟨hy.1, by simpa [I.left_inv] using hyv⟩, hy.2⟩
      have hst : modelSet I (u ∩ v) ∈ nhdsWithin y (modelSet I u) := by
        refine mem_nhdsWithin.mpr ?_
        refine ⟨I.symm ⁻¹' v, hv_open.preimage I.continuous_symm, ?_, ?_⟩
        · simpa [modelSet, I.left_inv] using hyv
        · intro z hz
          exact ⟨⟨hz.2.1, hz.1⟩, hz.2.2⟩
      have hderiv :
          fderivWithin ℝ (I ∘ f ∘ I.symm) (modelSet I u) y =
            fderivWithin ℝ (I ∘ f ∘ I.symm) (modelSet I (u ∩ v)) y :=
        fderivWithin_of_mem_nhdsWithin hst
          ((modelSet_uniqueDiffOn I hu) y hy) (hvcont.differentiableOn (by decide) y hyuv)
      have hdetEq :
          jacobianDetWithin (I ∘ f ∘ I.symm) (modelSet I u) y =
            jacobianDetWithin (I ∘ f ∘ I.symm) (modelSet I (u ∩ v)) y := by
        simp [jacobianDetWithin, hderiv]
      exact hdetEq.symm ▸ hvdet y hyuv
  congr {f g u} hu hfg hf := by
    rcases hf with ⟨hfcont, hfdet⟩
    refine ⟨?_, ?_⟩
    · refine hfcont.congr ?_
      intro x hx
      simp [Function.comp, hfg _ hx.1]
    · intro x hx
      have hEqOn :
          EqOn (I ∘ g ∘ I.symm) (I ∘ f ∘ I.symm) (modelSet I u) := by
        intro y hy
        have hy' : I.symm y ∈ u := hy.1
        simp [Function.comp, hfg _ hy']
      have hdetEq :
          jacobianDetWithin (I ∘ g ∘ I.symm) (modelSet I u) x =
            jacobianDetWithin (I ∘ f ∘ I.symm) (modelSet I u) x := by
        simp [jacobianDetWithin, fderivWithin_congr hEqOn (hEqOn hx)]
      exact hdetEq.symm ▸ hfdet x hx

/-- Orientation-preserving structure groupoid on a model with corners. -/
def orientationPreservingGroupoid : StructureGroupoid H :=
  (orientationPreservingPregroupoid I).groupoid

omit [FiniteDimensional ℝ E] in
theorem orientationPreservingGroupoid_le_contDiffGroupoid :
    orientationPreservingGroupoid I ≤ contDiffGroupoid 1 I := by
  rw [orientationPreservingGroupoid, contDiffGroupoid]
  refine groupoid_of_pregroupoid_le _ _ ?_
  intro f s hs
  exact hs.1

omit [FiniteDimensional ℝ E] in
theorem mem_orientationPreservingGroupoid_iff {e : OpenPartialHomeomorph H H} :
    e ∈ orientationPreservingGroupoid I ↔ OrientationPreservingOn I e e.source
      ∧ OrientationPreservingOn I e.symm e.target := Iff.rfl

omit [FiniteDimensional ℝ E] in
theorem ofSet_mem_orientationPreservingGroupoid {s : Set H} (hs : IsOpen s) :
    OpenPartialHomeomorph.ofSet s hs ∈ orientationPreservingGroupoid I := by
  rw [mem_orientationPreservingGroupoid_iff, OpenPartialHomeomorph.ofSet_symm]
  exact ⟨orientationPreservingOn_ofSet I hs, orientationPreservingOn_ofSet I hs⟩

instance : ClosedUnderRestriction (orientationPreservingGroupoid I) :=
  (closedUnderRestriction_iff_id_le _).mpr <| by
    rw [StructureGroupoid.le_iff]
    rintro e ⟨s, hs, hes⟩
    exact (orientationPreservingGroupoid I).mem_of_eqOnSource
      (ofSet_mem_orientationPreservingGroupoid I hs) hes

end Groupoid

section Orientable

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- A manifold is `Orientable` if its atlas is compatible with the
`orientationPreservingGroupoid`. -/
abbrev Orientable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  HasGroupoid M (orientationPreservingGroupoid I)

end Orientable

section Tangent

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The tangent-space orientation induced from an orientation of the model fiber. -/
noncomputable def tangentOrientation {x : M} [FiniteDimensional ℝ E]
    [Module.Oriented ℝ E (Fin (Module.finrank ℝ E))] :
    Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)) := by
  simpa [TangentSpace] using (positiveOrientation : Orientation ℝ E (Fin (Module.finrank ℝ E)))

end Tangent

end Manifold
