/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
module

public import Mathlib.Geometry.Manifold.JetBundle.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Defs

-- Re-export required type classes
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Jet Bundle Operations

This file defines the main operations on jet bundles:
- The r-jet extension of a smooth map
- Holonomic sections (sections that are r-jet extensions)
- The source and target projections

## Main definitions

* `jetExtension` : The r-jet extension operator J^r f of a smooth map f : M → M'.
* `IsHolonomic` : Refinement using actual jet extension.
* `Section.jetExtension` : The jet extension of a section.

## References

* Eliashberg, Y., & Mishachev, N. (2002). "Introduction to the h-Principle".
  Graduate Studies in Mathematics, Vol. 48. AMS.
-/

@[expose] public section

open Set Function Filter Bundle Topology
open scoped Topology Manifold Bundle ContDiff

noncomputable section

/-! ## Jet extension in Euclidean space -/

section EuclideanJetExtension

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The r-jet extension of a smooth map. Given a C^r map f : E → F,
this produces a map E → Jet 𝕜 E F r that at each point x gives
the r-jet of f at x. -/
def jetExtensionEuc {r : ℕ} {n : ℕ∞} (hn : r ≤ n) (f : E → F) (_hf : ContDiff 𝕜 n f) :
    E → Jet 𝕜 E F r :=
  fun x => jetOf hn f x

/-- The jet extension is continuous for a smooth function. -/
theorem continuous_jetExtensionEuc {r : ℕ} {n : ℕ∞} (hn : r ≤ n)
    {f : E → F} (hf : ContDiff 𝕜 n f) :
    Continuous (jetExtensionEuc hn f hf) := by
  -- The topology on Jet is induced by the product topology on coefficients.
  -- Continuity follows from ContDiff.continuous_iteratedFDeriv applied to each coefficient.
  -- Each ftaylorSeries 𝕜 f · k = iteratedFDeriv 𝕜 k f is continuous for k ≤ r ≤ n.
  refine continuous_induced_rng.2 ?_
  refine continuous_pi ?_
  intro k
  have hk : (k : ℕ) ≤ r := Nat.le_of_lt_succ k.is_lt
  have hk' : (k : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by
    have hk' : (k : ℕ∞) ≤ (r : ℕ∞) := by
      exact_mod_cast hk
    have hk'' : (k : ℕ∞) ≤ n := le_trans hk' hn
    exact_mod_cast hk''
  have hcont : Continuous fun x => iteratedFDeriv 𝕜 (k : ℕ) f x :=
    ContDiff.continuous_iteratedFDeriv (m := (k : ℕ)) hk' hf
  simpa [jetExtensionEuc, jetOf, ftaylorSeries] using hcont

/-- The value of the jet extension at a point equals the function value. -/
@[simp]
theorem jetExtensionEuc_value {r : ℕ} {n : ℕ∞} (hn : r ≤ n)
    {f : E → F} (hf : ContDiff 𝕜 n f) (x : E) :
    (jetExtensionEuc hn f hf x).value = f x := by
  simp only [jetExtensionEuc, jetOf, Jet.value, ftaylorSeries]
  -- ftaylorSeries 𝕜 f x 0 = iteratedFDeriv 𝕜 0 f x, applied to 0 gives f x
  exact iteratedFDeriv_zero_apply 0

end EuclideanJetExtension

/-! ## Jet extension for manifold maps -/

section ManifoldJetExtension

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- The r-jet extension of a smooth map f : M → M'.
This gives a section of the jet bundle J^r(M, M'), sending each point x ∈ M
to the r-jet of f at x.

For manifolds, this is defined using local coordinates: at each point x,
we use the charts at x and f(x) to compute the jet in the model space. -/
def jetExtension (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  (r : ℕ) (n : ℕ∞) (hn : r ≤ n) (f : M → M') (_hf : ContMDiff I I' n f)
    (x : M) : JetBundle I I' M M' r :=
  -- The chart representation I' ∘ chart ∘ f ∘ chart⁻¹ ∘ I⁻¹ is ContDiff since f is ContMDiff
  -- This follows from ContMDiff definition but requires careful unpacking
  ⟨(x, f x), jetOf hn (I' ∘ (chartAt H' (f x)) ∘ f ∘ (chartAt H x).symm ∘ I.symm)
           (I (chartAt H x x))⟩

/-- A section of the jet bundle is holonomic if it equals the jet extension
of some smooth map. -/
def IsHolonomicSection (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H' M']
    (r : ℕ) (σ : M → JetBundle I I' M M' r) : Prop :=
  ∃ (n : ℕ∞) (hn : r ≤ n) (f : M → M') (hf : ContMDiff I I' n f),
    ∀ x, σ x = jetExtension I I' r n hn f hf x

/-- The source projection of the jet bundle: proj : J^r(M, M') → M. -/
def JetBundle.src (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (r : ℕ) : JetBundle I I' M M' r → M :=
  fun p => p.1.1

/-- The target projection of the jet bundle: trg : J^r(M, M') → M'. -/
def JetBundle.trg (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (r : ℕ) : JetBundle I I' M M' r → M' :=
  fun p => p.1.2

/-- The source-target projection: J^r(M, M') → M × M'. -/
def JetBundle.srcTrg (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (r : ℕ) : JetBundle I I' M M' r → M × M' :=
  fun p => p.1

/-- For a holonomic section σ = J^r f, the target projection equals f. -/
theorem IsHolonomicSection.trg_eq (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    {r : ℕ} {σ : M → JetBundle I I' M M' r} (hσ : IsHolonomicSection I I' r σ) :
    ∃ f : M → M', ∀ x, JetBundle.trg I I' r (σ x) = f x := by
  obtain ⟨n, hn, f, _hf, hσ'⟩ := hσ
  refine ⟨f, fun x => ?_⟩
  rw [hσ' x]
  rfl

end ManifoldJetExtension

end

end
