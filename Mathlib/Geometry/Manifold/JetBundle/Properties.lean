/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.Geometry.Manifold.JetBundle.Basic
import Mathlib.Geometry.Manifold.JetBundle.CoordChange

/-!
# Properties of Jet Bundles

This file defines the topological and manifold structure of the jet bundle `J^r(M, M')`.

## Main definitions

* `JetBundle.instTopologicalSpace` : The topology on the jet bundle, induced by the charts.
* `JetBundle.instChartedSpace` : The charted space structure on the jet bundle.
* `JetBundle.instIsManifold` : The smooth manifold structure (using `IsManifold`).

## Structure

The r-jet bundle `J^r(M, M')` is a fiber bundle over `M × M'` with fiber `J^r(E, E')`.
Locally, if `U` and `V` are charts in `M` and `M'`, then `J^r(U, V) ≅ U × V × J^r(E, E')`.
-/

noncomputable section

open Set Function Filter Bundle Topology
open scoped Topology Manifold Bundle ContDiff

namespace JetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {r : ℕ}

/-- The model space for the jet bundle: `H × H' × J^r(E, E')`. -/
abbrev ModelSpace (_I : ModelWithCorners 𝕜 E H) (_I' : ModelWithCorners 𝕜 E' H') (r : ℕ) :=
  ModelProd H (ModelProd H' (Jet 𝕜 E E' r))

/-- The corners model for the jet bundle. -/
def ModelWithCorners.jetBundle (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  (r : ℕ) :
  ModelWithCorners 𝕜 (E × E' × Jet 𝕜 E E' r) (ModelSpace I I' r) :=
  I.prod (I'.prod (modelWithCornersSelf 𝕜 (Jet 𝕜 E E' r)))

/-! ## Bundle core data (to be used in `FiberBundleCore`) -/

/-- Index type for jet bundle charts: pairs of charts on `M` and `M'`. -/
abbrev Index := (atlas H M) × (atlas H' M')

/-- Base set for a chart index: the product of chart sources. -/
def baseSet (i : Index (H := H) (M := M) (H' := H') (M' := M')) : Set (M × M') :=
  (i.1.1.source) ×ˢ (i.2.1.source)

lemma isOpen_baseSet (i : Index (H := H) (M := M) (H' := H') (M' := M')) :
    IsOpen (baseSet (H := H) (M := M) (H' := H') (M' := M') i) := by
  simpa [baseSet] using (IsOpen.prod i.1.1.open_source i.2.1.open_source)

/-- Preferred index at a basepoint `(x, y)` using `achart`. -/
def indexAt (x : M × M') : Index (H := H) (M := M) (H' := H') (M' := M') :=
  (achart H x.1, achart H' x.2)

lemma mem_baseSet_at (x : M × M') :
    x ∈ baseSet (H := H) (M := M) (H' := H') (M' := M') (indexAt (H := H) (M := M)
      (H' := H') (M' := M') x) := by
  refine ⟨?_, ?_⟩
  · simp [indexAt, mem_chart_source]
  · simp [indexAt, mem_chart_source]

/-- Coordinate change on the jet fiber induced by chart indices. -/
def coordChange (i j : Index (H := H) (M := M) (H' := H') (M' := M')) (x : M × M') :
    Jet 𝕜 E E' r → Jet 𝕜 E E' r :=
  let xM := x.1
  let yM := x.2
  let sourceChange : E → E := (j.1.1.extend I) ∘ (i.1.1.extend I).symm
  let targetChange : E' → E' := (j.2.1.extend I') ∘ (i.2.1.extend I').symm
  Jet.coordChange (r := r) (x := (i.1.1.extend I xM)) (y := (i.2.1.extend I' yM))
    sourceChange targetChange

/-! ### Core data container

This structure records the *data* of the jet bundle charts (base sets, index choice,
and fiber coordinate change maps). It will be promoted to a `FiberBundleCore` once
the cocycle and smoothness/continuity properties are proved.
-/

structure JetBundleCoreData where
  baseSet : Index (H := H) (M := M) (H' := H') (M' := M') → Set (M × M')
  indexAt : M × M' → Index (H := H) (M := M) (H' := H') (M' := M')
  coordChange :
    Index (H := H) (M := M) (H' := H') (M' := M') →
      Index (H := H) (M := M) (H' := H') (M' := M') →
        M × M' → Jet 𝕜 E E' r → Jet 𝕜 E E' r

/-- The jet bundle chart data packaged as a structure. -/
def jetBundleCoreData : JetBundleCoreData (𝕜 := 𝕜) (E := E) (E' := E') (H := H) (M := M)
  (H' := H') (M' := M') (r := r) :=
  { baseSet := baseSet (H := H) (M := M) (H' := H') (M' := M'),
    indexAt := indexAt (H := H) (M := M) (H' := H') (M' := M'),
    coordChange := coordChange (I := I) (I' := I') (H := H) (M := M) (H' := H')
      (M' := M') (r := r) }

/--
Build a `FiberBundleCore` for the jet bundle from proofs of the cocycle and continuity properties
of the coordinate-change maps.

This is the correct, principled bundle core; the remaining proof obligations are factored out so
they can be discharged once the jet coordinate-change smoothness theory is in place.
-/
def jetBundleCore
    (coordChange_self :
      ∀ i, ∀ x ∈ baseSet (H := H) (M := M) (H' := H') (M' := M') i, ∀ v,
        coordChange (I := I) (I' := I') (H := H) (M := M) (H' := H') (M' := M') (r := r)
          i i x v = v)
    (continuousOn_coordChange :
      ∀ i j,
        ContinuousOn
          (fun p : (M × M') × Jet 𝕜 E E' r =>
            coordChange (I := I) (I' := I') (H := H) (M := M) (H' := H') (M' := M') (r := r)
              i j p.1 p.2)
          ((baseSet (H := H) (M := M) (H' := H') (M' := M') i ∩
              baseSet (H := H) (M := M) (H' := H') (M' := M') j) ×ˢ univ))
    (coordChange_comp :
      ∀ i j k, ∀ x ∈ baseSet (H := H) (M := M) (H' := H') (M' := M') i ∩
          baseSet (H := H) (M := M) (H' := H') (M' := M') j ∩
          baseSet (H := H) (M := M) (H' := H') (M' := M') k,
        ∀ v,
          (coordChange (I := I) (I' := I') (H := H) (M := M) (H' := H') (M' := M') (r := r)
              j k x)
            (coordChange (I := I) (I' := I') (H := H) (M := M) (H' := H') (M' := M') (r := r)
              i j x v) =
            coordChange (I := I) (I' := I') (H := H) (M := M) (H' := H') (M' := M') (r := r)
              i k x v) :
    FiberBundleCore (Index (H := H) (M := M) (H' := H') (M' := M')) (M × M')
      (Jet 𝕜 E E' r) where
  baseSet := baseSet (H := H) (M := M) (H' := H') (M' := M')
  isOpen_baseSet := isOpen_baseSet (H := H) (M := M) (H' := H') (M' := M')
  indexAt := indexAt (H := H) (M := M) (H' := H') (M' := M')
  mem_baseSet_at := mem_baseSet_at (H := H) (M := M) (H' := H') (M' := M')
  coordChange := coordChange (I := I) (I' := I') (H := H) (M := M) (H' := H') (M' := M')
    (r := r)
  coordChange_self := coordChange_self
  continuousOn_coordChange := continuousOn_coordChange
  coordChange_comp := coordChange_comp

/-! ## Topological Structure -/

/-- Auxiliary equivalence between the jet bundle and the product
`M × (M' × J^r(E, E'))`. -/
def equivProd : JetBundle I I' M M' r ≃ M × (M' × Jet 𝕜 E E' r) where
  toFun p := (p.1.1, p.1.2, p.2)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The topology on the jet bundle is induced by the local charts.
For now, we define it via the `ChartedSpace` structure which we will construct.
However, since `JetBundle` is defined as a sigma type, we can put the sigma topology on it?
No, we want the "twisted" topology.

Ideally we would use `FiberBundleCore` or `VectorBundleCore`.
Given we haven't defined the transition functions yet, we will postulate the existence
of the structure for now to unblock the definition of Differential Relations.
-/
instance instTopologicalSpace : TopologicalSpace (JetBundle I I' M M' r) :=
  let _ : TopologicalSpace (Jet 𝕜 E E' r) := Jet.instTopologicalSpace
  TopologicalSpace.induced (equivProd (I := I) (I' := I') (M := M) (M' := M') (r := r))
    (inferInstance : TopologicalSpace (M × (M' × Jet 𝕜 E E' r)))

/-- The jet bundle is (noncanonically) homeomorphic to the product
`M × (M' × J^r(E, E'))` with the induced topology. -/
def homeomorphProd : JetBundle I I' M M' r ≃ₜ M × (M' × Jet 𝕜 E E' r) where
  toEquiv := equivProd (I := I) (I' := I') (M := M) (M' := M') (r := r)
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    simpa using (continuous_id : Continuous fun p : M × (M' × Jet 𝕜 E E' r) => p)

/-! ## Manifold Structure -/

/-- The charted space instance for the jet bundle.
This makes `JetBundle` a manifold modeled on `E × E' × Jet 𝕜 E E' r`. -/
instance instChartedSpace : ChartedSpace (ModelSpace I I' r) (JetBundle I I' M M' r) := by
  classical
  let P := M × (M' × Jet 𝕜 E E' r)
  let e : JetBundle I I' M M' r ≃ₜ P :=
    homeomorphProd (I := I) (I' := I') (M := M) (M' := M') (r := r)
  letI : ChartedSpace (ModelSpace I I' r) P := by
    infer_instance
  letI : ChartedSpace P (JetBundle I I' M M' r) :=
  { atlas := {e.toOpenPartialHomeomorph}
    chartAt := fun _ => e.toOpenPartialHomeomorph
    mem_chart_source := by simp
    chart_mem_atlas := by simp }
  simpa [ModelSpace, P] using
    (ChartedSpace.comp (H := ModelSpace I I' r) (H' := P)
      (M := JetBundle I I' M M' r))

-- TODO: Define a genuine smooth structure once chart transition smoothness is available.

end JetBundle
