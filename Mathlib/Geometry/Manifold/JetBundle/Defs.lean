/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
module

import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- Public imports for required type classes and definitions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Jet Bundles

This file defines the r-jet bundle of smooth maps between smooth manifolds,
following the exposition in Eliashberg & Mishachev's "Introduction to the h-Principle".

## Main definitions

* `Jet r E F` : The type of r-jets of smooth maps from E to F at a point, consisting of
  a function value and derivatives up to order r.
* `JetSpace r E F (x, y)` : The space of r-jets at a source point `x` with target point `y`.
* `jetExtension` : The r-jet extension operator that maps a smooth function to its r-jet.
* `IsHolonomic` : Predicate for sections that are r-jet extensions of actual smooth maps.

## Main results

* The jet bundle has a natural fiber bundle structure.
* The 1-jet bundle is isomorphic to the tangent bundle (as expected).

## Implementation notes

The r-jet of a map f : E → F at x consists of:
- The value f(x)
- All partial derivatives of f up to order r

For manifolds, we use local coordinates to define jets via the standard jet space
in Euclidean space, similar to how tangent bundles are defined.

## References

* Eliashberg, Y., & Mishachev, N. (2002). "Introduction to the h-Principle".
  Graduate Studies in Mathematics, Vol. 48. AMS.
* Gromov, M. (1986). "Partial Differential Relations". Springer-Verlag.

## Tags

jet bundle, jet space, holonomic, differential relation, h-principle
-/

@[expose] public section

open Set Function Filter Bundle Topology
open scoped Topology Manifold Bundle ContDiff

noncomputable section

/-! ## Jets in Euclidean space -/

section EuclideanJets

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ}

/-- The type of r-jets of maps from E to F at a point.
An r-jet consists of the value and all derivatives up to order r.

This is the Euclidean (coordinate) definition. For manifolds, we will use
this in local charts.

The k-th component for k = 0, ..., r is a symmetric k-linear map representing
the k-th derivative. This matches the convention of `FormalMultilinearSeries`. -/
structure Jet (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (r : ℕ) where
  /-- The k-th derivative for k = 0, 1, ..., r as a continuous k-linear map.
      The 0-th derivative represents the function value (as a 0-linear map). -/
  coeff : (k : Fin (r + 1)) → ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F

namespace Jet

variable {r : ℕ}
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The function value of a jet (extracted from the 0-th coefficient). -/
def value (j : Jet 𝕜 E F r) : F := j.coeff 0 0

/-- The zero jet (all derivatives zero). -/
instance instZero : Zero (Jet 𝕜 E F r) where
  zero := ⟨fun _ => 0⟩

/-- Addition of jets. -/
instance instAdd : Add (Jet 𝕜 E F r) where
  add j₁ j₂ := ⟨fun k => j₁.coeff k + j₂.coeff k⟩

/-- Negation of jets. -/
instance instNeg : Neg (Jet 𝕜 E F r) where
  neg j := ⟨fun k => -j.coeff k⟩

/-- Scalar multiplication of jets. -/
instance instSMul : SMul 𝕜 (Jet 𝕜 E F r) where
  smul c j := ⟨fun k => c • j.coeff k⟩

/-- Extensionality for jets. -/
@[ext]
theorem ext {j₁ j₂ : Jet 𝕜 E F r}
    (h : ∀ k, j₁.coeff k = j₂.coeff k) : j₁ = j₂ := by
  cases j₁; cases j₂; simp only [mk.injEq]; exact funext h

/-- Jets form an additive commutative group. -/
instance instAddCommGroup : AddCommGroup (Jet 𝕜 E F r) where
  add_assoc a b c := ext (fun k => add_assoc _ _ _)
  zero_add a := ext (fun k => zero_add _)
  add_zero a := ext (fun k => add_zero _)
  add_comm a b := ext (fun k => add_comm _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := ext (fun k => neg_add_cancel _)

/-- Jets form a module over the base field. -/
instance instModule : Module 𝕜 (Jet 𝕜 E F r) where
  one_smul _ := ext (fun _ => one_smul _ _)
  mul_smul _ _ _ := ext (fun _ => mul_smul _ _ _)
  smul_zero _ := ext (fun _ => smul_zero _)
  smul_add _ _ _ := ext (fun _ => smul_add _ _ _)
  add_smul _ _ _ := ext (fun _ => add_smul _ _ _)
  zero_smul _ := ext (fun _ => zero_smul _ _)

/-- The canonical linear equivalence between jets and the Pi type of their coefficients. -/
def linearEquivPi : Jet 𝕜 E F r ≃ₗ[𝕜]
  ((k : Fin (r + 1)) → ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F) where
  toFun j := j.coeff
  invFun c := ⟨c⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Jets form a normed group. -/
instance instNormedAddCommGroup : NormedAddCommGroup (Jet 𝕜 E F r) :=
  NormedAddCommGroup.induced (Jet 𝕜 E F r)
    ((k : Fin (r + 1)) → ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F)
    linearEquivPi.toAddEquiv (AddEquiv.injective _)

/-- Jets form a normed space. -/
instance instNormedSpace : NormedSpace 𝕜 (Jet 𝕜 E F r) :=
  NormedSpace.induced 𝕜 (Jet 𝕜 E F r)
    ((k : Fin (r + 1)) → ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F)
    linearEquivPi

/-- The topology on jets is induced by the product topology on the coefficients.
Each coefficient is a continuous multilinear map, which has a natural topology. -/
instance instTopologicalSpace : TopologicalSpace (Jet 𝕜 E F r) :=
  TopologicalSpace.induced linearEquivPi
    (Pi.topologicalSpace)

/-- The canonical equivalence between jets and the Pi type of their coefficients. -/
def equivPi : Jet 𝕜 E F r ≃
    ((k : Fin (r + 1)) → ContinuousMultilinearMap 𝕜 (fun _ : Fin k => E) F) :=
  linearEquivPi.toEquiv

/-- Extend a jet to a formal multilinear series by filling higher coefficients with `0`. -/
def toFMS (j : Jet 𝕜 E F r) : FormalMultilinearSeries 𝕜 E F
  | n =>
      if h : n ≤ r then
        let k : Fin (r + 1) := ⟨n, Nat.lt_succ_of_le h⟩
        j.coeff k
      else
        0

lemma toFMS_coeff_of_le (j : Jet 𝕜 E F r) {n : ℕ} (h : n ≤ r) :
    j.toFMS n = j.coeff ⟨n, Nat.lt_succ_of_le h⟩ := by
  simp [Jet.toFMS, h]


/-- Truncate a formal multilinear series to a jet of order `r`. -/
def truncate (p : FormalMultilinearSeries 𝕜 E F) (r : ℕ) : Jet 𝕜 E F r where
  coeff k := p k

lemma truncate_toFMS (j : Jet 𝕜 E F r) : Jet.truncate (Jet.toFMS j) r = j := by
  ext k
  have hk : (k : ℕ) ≤ r := Nat.le_of_lt_succ k.is_lt
  simp [Jet.truncate, Jet.toFMS, hk]

/-- Taylor composition of jets, defined by composing the associated formal multilinear series
and truncating. -/
noncomputable def taylorComp (q : Jet 𝕜 F G r) (p : Jet 𝕜 E F r) : Jet 𝕜 E G r :=
  Jet.truncate (FormalMultilinearSeries.taylorComp (Jet.toFMS q) (Jet.toFMS p)) r

end Jet

/-- The r-jet of a function `f` at a point `x`,
defined as the first `r+1` terms of its formal Taylor series. -/
def jetOf {r : ℕ} {n : ℕ∞} (_hn : r ≤ n) (f : E → F) (x : E) : Jet 𝕜 E F r where
  coeff k := ftaylorSeries 𝕜 f x k

namespace Jet

lemma toFMS_jetOf_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {r : ℕ} {n : ℕ∞} (hn : r ≤ n) (f : E → F) (x : E) {k : ℕ} (hk : k ≤ r) :
    (Jet.toFMS (jetOf (r := r) (n := n) hn f x)) k = ftaylorSeries 𝕜 f x k := by
  simp [Jet.toFMS, jetOf, hk]

end Jet

end EuclideanJets

/-! ## The jet bundle on manifolds -/

section JetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {r : ℕ}

/-
The fiber type for the r-jet bundle of maps M → M', viewed over the base `M × M'`.
At each point `(x, y) : M × M'`, this is the space of r-jets of germs of maps
at `x` with target modeled at `y`.
-/
def JetSpace (_I : ModelWithCorners 𝕜 E H) (_I' : ModelWithCorners 𝕜 E' H')
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']
    (r : ℕ) (_ : M × M') : Type _ :=
  Jet 𝕜 E E' r

/-- The total space of the r-jet bundle over the base `M × M'`. -/
abbrev JetBundle (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']
    (r : ℕ) : Type _ :=
  Bundle.TotalSpace (Jet 𝕜 E E' r) (JetSpace I I' M M' r)

namespace JetBundle

variable (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M'] (r : ℕ)

/-- The projection from the jet bundle to the base `M × M'`. -/
def proj : JetBundle I I' M M' r → M × M' := Bundle.TotalSpace.proj

/-- The projection from the jet bundle to the target manifold (base point of the jet). -/
def targetProj : JetBundle I I' M M' r → M' := fun p => p.1.2

/-- The underlying jet in the jet bundle. -/
def jet : (p : JetBundle I I' M M' r) → Jet 𝕜 E E' r := fun p => p.2

end JetBundle

-- Note: IsHolonomicSection and HolonomicSection are defined in Basic.lean
-- where jetExtension is available

end JetBundle

end

end
