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
def homeomorph {s : Set E} {f : E → E'} (hf : ContinuousOn f s) :
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
def homeomorph' {f : E → E'} (hf : Continuous f) : (Set.univ.graphOn f) ≃ₜ E :=
  (homeomorph hf.continuousOn).trans (Homeomorph.Set.univ E)

/--
The inverse homeomorphism: embedding the domain into its graph.

Maps `x ∈ s` to `(x, f(x)) ∈ graph(f)`.
-/
def toHomeomorph {s : Set E} {f : E → E'} (hf : ContinuousOn f s) : s ≃ₜ s.graphOn f :=
  (homeomorph hf).symm

section Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {n : WithTop ℕ∞}

/--
The graph of a continuous function inherits a `ChartedSpace` structure from the domain.

Given `f : H → E'` continuous on `s ⊆ H`, the graph `s.graphOn f` is charted over `H`
by composing charts of `s` with the homeomorphism from graph to `s`.
-/
def instChartedSpace {s : Set H} {f : H → E'} (hf : ContinuousOn f s)
    [cs : ChartedSpace H s] : ChartedSpace H (s.graphOn f) where
  atlas := { (homeomorph hf).toOpenPartialHomeomorph.trans e | e ∈ cs.atlas }
  chartAt x := (homeomorph hf).toOpenPartialHomeomorph.trans
    (cs.chartAt (homeomorph hf x))
  mem_chart_source x := by
    simp
  chart_mem_atlas x := by
    simp only [mem_setOf_eq]
    exact ⟨cs.chartAt (homeomorph hf x), cs.chart_mem_atlas _, rfl⟩

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
  letI csGraph := instChartedSpace hf
  have compat : ∀ {e e' : OpenPartialHomeomorph (s.graphOn f) H},
      e ∈ csGraph.atlas → e' ∈ csGraph.atlas → e.symm.trans e' ∈ contDiffGroupoid n I := by
    rintro e e' ⟨e0, he0_mem, rfl⟩ ⟨e0', he0'_mem, rfl⟩
    have h_grp := (contDiffGroupoid n I).compatible he0_mem he0'_mem
    apply (contDiffGroupoid n I).mem_of_eqOnSource h_grp
    let gH := homeomorph hf
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
        refine ⟨⟨hx1, trivial⟩, ?_⟩
        simpa only [OpenPartialHomeomorph.trans_apply,
          Homeomorph.toOpenPartialHomeomorph_symm_apply] using hx2
    · -- function equality on source
      intro x hx
      simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
                 OpenPartialHomeomorph.trans_apply,
                 Homeomorph.toOpenPartialHomeomorph_symm_apply,
                 Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.apply_symm_apply]
  haveI : HasGroupoid (H := H) (M := s.graphOn f) (contDiffGroupoid n I) := ⟨compat⟩
  exact IsManifold.mk' I n (s.graphOn f)

omit [NormedSpace 𝕜 E'] in
/-- Smoothness of the graph-domain homeomorphism and its inverse for the induced manifold
structure on the graph. -/
theorem contMDiff_homeomorph {s : Set H} {f : H → E'} (hf : ContinuousOn f s)
    [ChartedSpace H s] [IsManifold I n s] :
    let _ := instChartedSpace hf
    let _ : IsManifold I n (s.graphOn f) := instIsManifold I hf
    ContMDiff I I n (homeomorph hf) ∧ ContMDiff I I n (homeomorph hf).symm := by
  letI csGraph := instChartedSpace hf
  letI : IsManifold I n (s.graphOn f) := instIsManifold I hf
  let h := (homeomorph hf).toOpenPartialHomeomorph
  have hStruct :
      ChartedSpace.LiftPropOn (contDiffGroupoid n I).IsLocalStructomorphWithinAt h h.source := by
    intro x hx
    refine ⟨h.continuousAt hx |>.continuousWithinAt, fun hx' => ?_⟩
    let c : OpenPartialHomeomorph s H := chartAt H (h x)
    let e : OpenPartialHomeomorph H H := (chartAt H x).symm.trans (h.trans c)
    refine ⟨e, ?_, ?_, ?_⟩
    · exact (contDiffGroupoid n I).compatible (chart_mem_atlas H x) (by
        dsimp [h, c]
        exact ⟨chartAt H (homeomorph hf x),
          chart_mem_atlas H (homeomorph hf x), rfl⟩)
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
theorem contMDiff_subtype_val_iff {s : Set H} {f : H → E'} (hf : ContinuousOn f s)
    {m n : WithTop ℕ∞} [ChartedSpace H s] [IsManifold I n s] (hmn : m ≤ n)
    (hval : ContMDiff I I m (Subtype.val : s → H)) :
    let _ := instChartedSpace hf
    ContMDiff I (I.prod (modelWithCornersSelf 𝕜 E')) m
      (Subtype.val : s.graphOn f → H × E') ↔
    ContMDiff I (modelWithCornersSelf 𝕜 E') m (fun x : s ↦ f x) := by
  letI : IsManifold I m s := IsManifold.of_le hmn
  letI csGraph := instChartedSpace hf
  letI : IsManifold I m (s.graphOn f) := instIsManifold I hf
  have hHomeo :
      ContMDiff I I m (homeomorph hf) ∧
        ContMDiff I I m (homeomorph hf).symm :=
      contMDiff_homeomorph I hf
  -- The inclusion factors: Subtype.val = (fun x ↦ (x, f x)) ∘ homeomorph
  have factorization : (Subtype.val : s.graphOn f → H × E') =
      (fun x : s => (x.val, f x.val)) ∘ (homeomorph hf) := by
    ext z <;> rcases z with ⟨⟨x, y⟩, hxy⟩ <;>
      simp [Function.comp_apply, homeomorph, (mem_graphOn.mp hxy).2]
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
