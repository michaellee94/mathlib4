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
* `Set.graphOn.homeomorph'`: Special case for globally continuous functions, proving
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
def homeomorph {s : Set E} (f : E → E') (hf : ContinuousOn f s) :
    s.graphOn f ≃ₜ s where
  toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, (mem_graphOn.mp hx).1⟩
  invFun := fun ⟨x, hx⟩ => ⟨(x, f x), mem_graphOn.mpr ⟨hx, rfl⟩⟩
  left_inv := fun ⟨⟨x, y⟩, hxy⟩ => by
    simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
    exact (mem_graphOn.mp hxy).2
  right_inv := fun _ => rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Continuous.prodMk continuous_subtype_val
      (hf.comp_continuous continuous_subtype_val fun x => x.2)

/--
The graph of a globally continuous function `f : E → E'` is homeomorphic to `E`.

Special case of `graphOn.homeomorph` when the domain is the whole space.
-/
def homeomorph' (f : E → E') (hf : Continuous f) :
    (Set.univ.graphOn f) ≃ₜ E :=
  (homeomorph f hf.continuousOn).trans (Homeomorph.Set.univ E)

/--
The inverse homeomorphism: embedding the domain into its graph.

Maps `x ∈ s` to `(x, f(x)) ∈ graph(f)`.
-/
def toHomeomorph {s : Set E} (f : E → E') (hf : ContinuousOn f s) :
    s ≃ₜ s.graphOn f :=
  (homeomorph f hf).symm

section Manifold

variable {K : Type*} [NontriviallyNormedField K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace K E']
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners K E H)
  {n : WithTop ℕ∞}

/--
The graph of a continuous function inherits a `ChartedSpace` structure from the domain.

Given `f : H → E'` continuous on `s ⊆ H`, the graph `s.graphOn f` is charted over `H`
by composing charts of `s` with the homeomorphism from graph to `s`.
-/
def instChartedSpace {s : Set H} (f : H → E') (hf : ContinuousOn f s)
    [cs : ChartedSpace H s] : ChartedSpace H (s.graphOn f) where
  atlas := { (homeomorph f hf).toOpenPartialHomeomorph.trans e | e ∈ cs.atlas }
  chartAt x := (homeomorph f hf).toOpenPartialHomeomorph.trans
    (cs.chartAt (homeomorph f hf x))
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
        mem_inter_iff]
    exact ⟨mem_univ _, mem_chart_source H (homeomorph f hf x)⟩
  chart_mem_atlas x := by
    simp only [mem_setOf_eq]
    exact ⟨cs.chartAt (homeomorph f hf x), cs.chart_mem_atlas _, rfl⟩

omit [NormedSpace K E'] in
/--
The graph of a continuous function on a manifold is itself a manifold.

This follows from the fact that the graph is homeomorphic to the domain,
so chart transitions factor through the homeomorphism which cancels.
-/
theorem instIsManifold {s : Set H} (f : H → E') (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    @IsManifold K _ E _ _ H _ I n (s.graphOn f) _ (instChartedSpace f hf) := by
  letI csGraph := instChartedSpace f hf
  have compat : ∀ {e e' : OpenPartialHomeomorph (s.graphOn f) H},
      e ∈ csGraph.atlas → e' ∈ csGraph.atlas → e.symm.trans e' ∈ contDiffGroupoid n I := by
    intro e e' he he'
    simp only [csGraph, instChartedSpace, mem_setOf_eq] at he he'
    obtain ⟨e0, he0_mem, rfl⟩ := he
    obtain ⟨e0', he0'_mem, rfl⟩ := he'
    have h_grp := (contDiffGroupoid n I).compatible he0_mem he0'_mem
    apply (contDiffGroupoid n I).mem_of_eqOnSource h_grp
    let gH := homeomorph f hf
    constructor
    · -- source equality
      ext x
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
                 OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
                 Homeomorph.toOpenPartialHomeomorph_source,
                 Homeomorph.toOpenPartialHomeomorph_target,
                 mem_inter_iff, mem_preimage, univ_inter]
      constructor
      · intro ⟨hx1, hx2⟩
        simp only [OpenPartialHomeomorph.trans_apply,
                   Homeomorph.toOpenPartialHomeomorph_symm_apply] at hx2
        constructor
        · exact hx1.1
        · convert hx2 using 1
      · intro ⟨hx1, hx2⟩
        constructor
        · exact ⟨hx1, trivial⟩
        · simp only [OpenPartialHomeomorph.trans_apply,
                     Homeomorph.toOpenPartialHomeomorph_symm_apply]
          exact hx2
    · -- function equality on source
      intro x hx
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
                 OpenPartialHomeomorph.trans_apply,
                 Homeomorph.toOpenPartialHomeomorph_symm_apply,
                 Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.apply_symm_apply]
  haveI : @HasGroupoid H _ (s.graphOn f) _ csGraph (contDiffGroupoid n I) := ⟨compat⟩
  exact @IsManifold.mk' K _ E _ _ H _ I n (s.graphOn f) _ csGraph this

omit [NormedSpace K E'] in
/-- Smoothness of the graph-domain homeomorphism and its inverse for the induced manifold
structure on the graph. -/
theorem contMDiff_homeomorph {s : Set H} (f : H → E') (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    let _ := instChartedSpace f hf
    let _ : IsManifold I n (s.graphOn f) := instIsManifold I f hf
    ContMDiff I I n (homeomorph f hf) ∧ ContMDiff I I n (homeomorph f hf).symm := by
  letI csGraph := instChartedSpace f hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I f hf
  let h := (homeomorph f hf).toOpenPartialHomeomorph
  have hStruct :
      ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt h h.source := by
    intro x hx
    refine ⟨h.continuousAt hx |>.continuousWithinAt, ?_⟩
    intro hx'
    let c : OpenPartialHomeomorph s H := chartAt H (h x)
    let e : OpenPartialHomeomorph H H := (chartAt H x).symm.trans (h.trans c)
    refine ⟨e, ?_, ?_, ?_⟩
    · exact (contDiffGroupoid n I).compatible (chart_mem_atlas (H := H) x) (by
        dsimp [h, c]
        exact ⟨chartAt H (homeomorph f hf x), chart_mem_atlas (H := H) (homeomorph f hf x), rfl⟩)
    · intro y hy
      simp [e, c, h] at hy ⊢
    · simp [e, c, h]
  simpa [h, contMDiffOn_univ] using (isLocalStructomorphOn_contDiffGroupoid_iff h).1 hStruct

/--
If `s` is a `C^n` manifold and `m ≤ n`, then the inclusion map from the graph into the ambient
product space is `C^m` if and only if the graph function is `C^m` on `s`.

This characterizes when the graph, with the manifold structure inherited from the domain,
is a `C^m` submanifold of the product space `H × E'`, assuming
`Subtype.val : s → H` is `C^m`.
-/
theorem contMDiff_subtype_val_iff {s : Set H} (f : H → E') (hf : ContinuousOn f s)
    {m n : WithTop ℕ∞} [ChartedSpace H s] [IsManifold I n s] (hmn : m ≤ n)
    (hval : ContMDiff I I m (Subtype.val : s → H)) :
    let _ := instChartedSpace f hf
    ContMDiff I (I.prod (modelWithCornersSelf K E')) m
      (Subtype.val : s.graphOn f → H × E') ↔
    ContMDiff I (modelWithCornersSelf K E') m (fun x : s ↦ f x) := by
  letI : IsManifold I m s := IsManifold.of_le hmn
  letI csGraph := instChartedSpace f hf
  letI : IsManifold I m (s.graphOn f) := instIsManifold I f hf
  have hHomeo : ContMDiff I I m (homeomorph f hf) ∧ ContMDiff I I m (homeomorph f hf).symm :=
      contMDiff_homeomorph I f hf
  -- The inclusion factors: Subtype.val = (fun x ↦ (x, f x)) ∘ homeomorph
  have factorization : (Subtype.val : s.graphOn f → H × E') =
      (fun x : s => (x.val, f x.val)) ∘ (homeomorph f hf) := by
    ext z <;> rcases z with ⟨⟨x, y⟩, hxy⟩
    · rfl
    · simpa [Function.comp_apply, homeomorph] using (mem_graphOn.mp hxy).2.symm
  rw [factorization]
  constructor
  · intro h
    have hcomp := h.comp hHomeo.2
    simp only [Function.comp_assoc, Homeomorph.self_comp_symm, Function.comp_id] at hcomp
    rw [contMDiff_prod_iff] at hcomp
    simpa [Function.comp_apply] using hcomp.2
  · intro hf_smooth
    apply ContMDiff.comp _ hHomeo.1
    rw [contMDiff_prod_iff]
    constructor
    · simpa [Function.comp_apply] using hval
    · simpa [Function.comp_apply] using hf_smooth

end Manifold

end Set.graphOn
