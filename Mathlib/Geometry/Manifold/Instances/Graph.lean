/-
Copyright (c) 2026 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Graphs of Continuous Functions as Manifolds

This file proves that the graph of a continuous function is homeomorphic to its domain,
and that it inherits a manifold structure when the domain is a manifold.

## Main Results

* `Set.graphOn.homeomorph`: The graph of a continuous function `f : E → E'` restricted to `s`,
  with the subspace topology, is homeomorphic to `s`.
* `Set.graphOn.homeomorph_univ`: Special case for globally continuous functions, proving
  `univ.graphOn f ≃ₜ E`.
* `Set.graphOn.instChartedSpace`: The graph inherits a `ChartedSpace` structure from the domain.
* `Set.graphOn.instIsManifold`: The graph is a smooth manifold when the domain is.
* `Set.graphOn.contMDiff_subtype_val_iff`: Smoothness of graph inclusion is equivalent to
  smoothness of the graph function on the domain manifold.

## Implementation Notes

The key insight is that the projection `(x, f(x)) ↦ x` is a homeomorphism from the graph to the
domain. Chart transitions on the graph factor through this homeomorphism, and since the
homeomorphism cancels in the composition, chart compatibility follows from compatibility in
the domain.
-/

@[expose] public section

open Set Topology

namespace Set.graphOn

variable {E E' : Type*} [TopologicalSpace E] [TopologicalSpace E']

/--
The graph of a continuous function `f : s → E'`, viewed as a subtype of `E × E'`,
is homeomorphic to `s` via the projection onto the first factor.
-/
def homeomorph {s : Set E} {f : E → E'} (hf : ContinuousOn f s) : s.graphOn f ≃ₜ s where
  toFun := fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, (mem_graphOn.mp hx).1⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨(x, f x), mem_graphOn.mpr ⟨hx, rfl⟩⟩
  left_inv := fun ⟨⟨x, y⟩, hxy⟩ ↦ by
    simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
    exact (mem_graphOn.mp hxy).2
  right_inv := fun _ ↦ rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Continuous.prodMk continuous_subtype_val
      (hf.comp_continuous continuous_subtype_val fun x ↦ x.2)

@[simp]
theorem homeomorph_apply {s : Set E} {f : E → E'} (hf : ContinuousOn f s) (x : s.graphOn f) :
    homeomorph hf x = ⟨x.1.1, (mem_graphOn.mp x.2).1⟩ := rfl

@[simp]
theorem homeomorph_symm_apply {s : Set E} {f : E → E'} (hf : ContinuousOn f s) (x : s) :
    (homeomorph hf).symm x = ⟨(x, f x), mem_graphOn.mpr ⟨x.2, rfl⟩⟩ := rfl

/--
The graph of a globally continuous function `f : E → E'` is homeomorphic to `E`.

Special case of `graphOn.homeomorph` when the domain is the whole space.
-/
def homeomorph_univ {f : E → E'} (hf : Continuous f) : (Set.univ.graphOn f) ≃ₜ E :=
  (homeomorph hf.continuousOn).trans (Homeomorph.Set.univ E)

@[simp]
theorem homeomorph_univ_apply {f : E → E'} (hf : Continuous f) (x : Set.univ.graphOn f) :
    homeomorph_univ hf x = x.1.1 := by simp [homeomorph_univ]

@[simp]
theorem homeomorph_univ_symm_apply {f : E → E'} (hf : Continuous f) (x : E) :
    (homeomorph_univ hf).symm x = ⟨(x, f x), mem_graphOn.mpr ⟨by simp, rfl⟩⟩ := by
  simp [homeomorph_univ]

section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {n : WithTop ℕ∞}

/--
The graph of a continuous function inherits a `ChartedSpace` structure from the domain.

Given `f : H → E'` continuous on `s ⊆ H`, the graph `s.graphOn f` is charted over `H`
by composing charts of `s` with the homeomorphism from graph to `s`.
-/
def instChartedSpace {s : Set H} {f : H → E'} (hf : ContinuousOn f s) [ChartedSpace H s] :
    ChartedSpace H (s.graphOn f) where
  atlas := { (homeomorph hf).toOpenPartialHomeomorph.trans e | e ∈ atlas H s }
  chartAt x := (homeomorph hf).toOpenPartialHomeomorph.trans (chartAt H (homeomorph hf x))
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt H (homeomorph hf x), chart_mem_atlas H _, rfl⟩

omit [NormedSpace 𝕜 E'] in
/--
The graph of a continuous function on a manifold is itself a manifold.

This follows from the fact that the graph is homeomorphic to the domain,
so chart transitions factor through the homeomorphism which cancels.
-/
theorem instIsManifold {s : Set H} {f : H → E'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    let _ := instChartedSpace hf
    IsManifold I n (s.graphOn f) := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace hf
  have compat : ∀ {e e' : OpenPartialHomeomorph (s.graphOn f) H},
      e ∈ atlas H (s.graphOn f) →
        e' ∈ atlas H (s.graphOn f) → e.symm.trans e' ∈ contDiffGroupoid n I := by
    rintro e e' ⟨e0, he0_mem, rfl⟩ ⟨e0', he0'_mem, rfl⟩
    have h_grp := (contDiffGroupoid n I).compatible he0_mem he0'_mem
    apply (contDiffGroupoid n I).mem_of_eqOnSource h_grp
    refine ⟨?_, ?_⟩
    · -- source equality
      ext x
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
                 OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
                 univ_inter]
      constructor <;> rintro ⟨hx1, hx2⟩
      · exact ⟨hx1.1, hx2⟩
      · exact ⟨⟨hx1, trivial⟩, hx2⟩
    · -- function equality on source
      intro x hx; simp
  haveI : HasGroupoid (H := H) (M := s.graphOn f) (contDiffGroupoid n I) := ⟨compat⟩
  exact IsManifold.mk' I n (s.graphOn f)

omit [NormedSpace 𝕜 E'] in
private theorem homeomorph_liftPropOn {s : Set H} {f : H → E'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace hf
    ChartedSpace.LiftPropOn
      (contDiffGroupoid n I).IsLocalStructomorphWithinAt
      (homeomorph hf).toOpenPartialHomeomorph
      (homeomorph hf).toOpenPartialHomeomorph.source := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  change ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt h h.source
  intro x hx
  refine ⟨h.continuousAt hx |>.continuousWithinAt, fun _ ↦ ?_⟩
  let e : OpenPartialHomeomorph H H := (chartAt H x).symm.trans (h.trans (chartAt H (h x)))
  refine ⟨e, ?_, (by intro y hy; simp [e, h] at hy ⊢), by simp [e, h]⟩
  exact (contDiffGroupoid n I).compatible (chart_mem_atlas H x) (by
    dsimp [h, e]
    exact ⟨chartAt H (homeomorph hf x), chart_mem_atlas H (homeomorph hf x), rfl⟩)

omit [NormedSpace 𝕜 E'] in
/-- Smoothness of the graph-domain homeomorphism for the induced manifold structure on the
graph. -/
theorem contMDiff_homeomorph_toFun {s : Set H} {f : H → E'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace hf
    ContMDiff I I n (homeomorph hf) := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  simpa [h, contMDiffOn_univ] using
    ((isLocalStructomorphOn_contDiffGroupoid_iff h).1 (homeomorph_liftPropOn I hf)).1

omit [NormedSpace 𝕜 E'] in
/-- Smoothness of the inverse graph-domain homeomorphism for the induced manifold structure on the
graph. -/
theorem contMDiff_homeomorph_invFun {s : Set H} {f : H → E'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    letI := instChartedSpace hf
    ContMDiff I I n (homeomorph hf).symm := by
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  simpa [h, contMDiffOn_univ] using
    ((isLocalStructomorphOn_contDiffGroupoid_iff h).1 (homeomorph_liftPropOn I hf)).2

/--
If `s` is a `C^n` manifold and `m ≤ n`, then the inclusion map from the graph into the ambient
product space is `C^m` if and only if the graph function is `C^m` on `s`.

This characterizes when the graph, with the manifold structure inherited from the domain,
is a `C^m` submanifold of the product space `H × E'`, assuming
`Subtype.val : s → H` is `C^m`.
-/
theorem contMDiff_subtype_val_iff {s : Set H} {f : H → E'} (hf : ContinuousOn f s)
    {m n : WithTop ℕ∞} [ChartedSpace H s] [IsManifold I n s] (hmn : m ≤ n)
    (hval : ContMDiff I I m (Subtype.val : s → H)) :
    let _ := instChartedSpace hf
    ContMDiff I (I.prod (modelWithCornersSelf 𝕜 E')) m
      (Subtype.val : s.graphOn f → H × E') ↔
    ContMDiff I (modelWithCornersSelf 𝕜 E') m (fun x : s ↦ f x) := by
  letI : IsManifold I m s := IsManifold.of_le hmn
  letI : ChartedSpace H (s.graphOn f) := instChartedSpace hf
  -- The inclusion factors: Subtype.val = (fun x ↦ (x, f x)) ∘ homeomorph
  have factorization : (Subtype.val : s.graphOn f → H × E') =
      (fun x : s ↦ (x.val, f x.val)) ∘ (homeomorph hf) := by
    ext z <;> rcases z with ⟨⟨x, y⟩, hxy⟩ <;>
      simp [Function.comp_apply, (mem_graphOn.mp hxy).2]
  rw [factorization]
  constructor
  · intro h
    have hcomp := h.comp (contMDiff_homeomorph_invFun I hf)
    simp only [Function.comp_assoc, Homeomorph.self_comp_symm, Function.comp_id] at hcomp
    rw [contMDiff_prod_iff] at hcomp
    simpa [Function.comp_apply] using hcomp.2
  · intro hf_smooth
    apply ContMDiff.comp _ (contMDiff_homeomorph_toFun I hf)
    rw [contMDiff_prod_iff]
    constructor
    · simpa [Function.comp_apply] using hval
    · simpa [Function.comp_apply] using hf_smooth

end Manifold

end Set.graphOn
