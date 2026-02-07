/-
Copyright (c) 2026 Michael Lee.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Projective-space charts from separating duals

This file develops affine charts on projective space from continuous linear
functionals.

Main steps:
* define `continuous_dual_separates_points` and normalize to value `1`,
* build the affine chart `affineChart` on `ℙ K V`,
* in the normed setting, transport chart targets to a fixed model space `F`,
* build `ChartedSpace` and `IsManifold ... ω` instances under `SeparatingDual`
  and `HyperplaneModel`.
-/

noncomputable section

@[expose] public section

open Projectivization Topology
open scoped LinearAlgebra.Projectivization ContDiff Manifold

variable {K : Type*} {V : Type*}

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [TopologicalSpace K] [TopologicalSpace V]
variable [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] [ContinuousSMul K V]

namespace Projectivization



/-- The topology on the projectivization is the quotient topology. -/
instance : TopologicalSpace (ℙ K V) :=
  letI : TopologicalSpace { v : V // v ≠ 0 } := instTopologicalSpaceSubtype
  instTopologicalSpaceQuotient

/-- Scalar multiplication by a unit is a homeomorphism of `V \ {0}`. -/
def smulHomeomorph (c : Kˣ) : {x : V // x ≠ 0} ≃ₜ {x : V // x ≠ 0} where
  toFun x := ⟨c • x.1, smul_ne_zero (Units.ne_zero c) x.2⟩
  invFun x := ⟨c⁻¹ • x.1, smul_ne_zero (Units.ne_zero _) x.2⟩
  left_inv x := Subtype.ext <| by simp only [smul_smul, inv_mul_cancel, one_smul]
  right_inv x := Subtype.ext <| by simp only [smul_smul, mul_inv_cancel, one_smul]
  continuous_toFun := (continuous_subtype_val.const_smul (c : K)).subtype_mk _
  continuous_invFun := (continuous_subtype_val.const_smul ((c⁻¹ : Kˣ) : K)).subtype_mk _

omit [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] in
/-- The projection map from V \ {0} to P(V) is an open map. -/
theorem isOpenMap_mk : IsOpenMap (fun (v : {x : V // x ≠ 0}) ↦ mk' K v) := by
  intro U hU
  rw [isOpen_coinduced]
  change IsOpen (mk' K ⁻¹' (mk' K '' U))
  -- The preimage of the image is the union over all unit scalings.
  have : mk' K ⁻¹' (mk' K '' U) = ⋃ (c : Kˣ), (smulHomeomorph c) '' U := by
    ext v
    constructor
    · rintro ⟨u, hu, hua⟩
      rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff] at hua
      rcases hua with ⟨c, hc⟩
      -- Rewrite a representative equation to exhibit membership in a scaled copy of `U`.
      refine Set.mem_iUnion.2 ⟨c⁻¹, ?_⟩
      refine ⟨u, hu, ?_⟩
      ext
      dsimp [smulHomeomorph]
      rw [inv_smul_eq_iff]
      exact hc.symm
    · intro h
      rcases Set.mem_iUnion.1 h with ⟨c, u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff]
      use c⁻¹
      dsimp [smulHomeomorph]
      simp [smul_smul]
  rw [this]
  apply isOpen_iUnion
  intro c
  exact (smulHomeomorph c).isOpenMap _ hU

/-! Predicate: the continuous dual separates points. -/

section SeparatingDual

variable [IsTopologicalDivisionRing K]

/-- Right multiplication by a scalar as a continuous linear endomorphism. -/
def mulRightCLM (a : K) : K →L[K] K where
  toLinearMap := LinearMap.mulRight K a
  cont := by
    simpa [LinearMap.mulRight_apply] using (continuous_mul_right a)

/-- The continuous dual `V →L[K] K` separates points of `V`.

Equivalently, for every nonzero `v : V`, there is `f : V →L[K] K` with `f v ≠ 0`. -/
def continuous_dual_separates_points : Prop := ∀ v : V, v ≠ 0 → ∃ f : V →L[K] K, f v ≠ 0

omit [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] [ContinuousSMul K V] in
/-- The continuous dual separates points iff every nonzero vector admits
    a continuous linear functional taking value `1`. -/
theorem continuous_dual_separates_points_iff_exists_eq_one :
    continuous_dual_separates_points (K := K) (V := V) ↔
      (∀ v : V, v ≠ 0 → ∃ f : V →L[K] K, f v = 1) := by
  constructor
  · intro h v hv
    rcases h v hv with ⟨f, hf⟩
    refine ⟨(mulRightCLM (f v)⁻¹).comp f, ?_⟩
    simp [mulRightCLM, hf, mul_inv_cancel₀]
  · intro h v hv
    rcases h v hv with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simp [hf]

end SeparatingDual

/-- Domain of the affine chart associated with `f`: points where `f` does not vanish. -/
def affineChartDomain (f : V →L[K] K) : Set (ℙ K V) :=
  mk' K '' {v | f v ≠ 0}

variable [IsTopologicalDivisionRing K] [T1Space K]

omit [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] [IsTopologicalDivisionRing K] in
/-- The domain of an affine chart is open. -/
theorem isOpen_affineChartDomain (f : V →L[K] K) : IsOpen (affineChartDomain f) := by
  rw [affineChartDomain]
  exact isOpenMap_mk ({u : {x : V // x ≠ 0} | f u ≠ 0}) (by
  have h_cont : Continuous fun u : {x : V // x ≠ 0} => f u :=
    f.continuous.comp continuous_subtype_val
  have h_eq :
      ({u : {x : V // x ≠ 0} | f u ≠ 0}) =
        (fun u : {x : V // x ≠ 0} => f u) ⁻¹' ({0} : Set K)ᶜ := by
    ext u
    simp
  rw [h_eq]
  exact (isClosed_singleton.preimage h_cont).isOpen_compl)

omit [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] [ContinuousSMul K V]
    [IsTopologicalDivisionRing K] [T1Space K] in
/-- Characterization of chart-domain membership for a canonical projective representative. -/
theorem mk'_mem_affineChartDomain_iff (f : V →L[K] K) (u : {x : V // x ≠ 0}) :
    mk' K u ∈ affineChartDomain f ↔ f u ≠ 0 := by
  constructor
  · rintro ⟨w, hw, hwu⟩
    rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff] at hwu
    rcases hwu with ⟨c, hc⟩
    intro hu
    apply hw
    have h1 : f ((c : K) • (u : V)) = f (w : V) := by
      simpa [Units.smul_def] using congrArg f hc
    rw [← h1, map_smul, smul_eq_mul, hu, mul_zero]
  · intro hu
    exact ⟨u, hu, rfl⟩

omit [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] [ContinuousSMul K V]
    [IsTopologicalDivisionRing K] [T1Space K] in
/-- Characterization of chart-domain membership for `mk K u hu`. -/
theorem mk_mem_affineChartDomain_iff (f : V →L[K] K) (u : V) (hu : u ≠ 0) :
    mk K u hu ∈ affineChartDomain f ↔ f u ≠ 0 := by simpa [mk'_eq_mk]
      using (mk'_mem_affineChartDomain_iff f ⟨u, hu⟩)

open LinearMap

/-- Raw representative formula for the affine chart map. -/
noncomputable def chartRaw (f : V →L[K] K) (v : V) : {x : V // x ≠ 0} → V := by
  classical
  exact fun u => if f (u : V) = 0 then 0 else (f (u : V))⁻¹ • (u : V) - v

omit [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] [ContinuousSMul K V]
    [IsTopologicalDivisionRing K] [T1Space K] in
/-- `chartRaw` is invariant under the projective equivalence relation. -/
theorem chartRaw_wd (f : V →L[K] K) (v : V) :
    ∀ (u w : {x : V // x ≠ 0}) (c : K), (u : V) = c • (w : V) →
      chartRaw f v u = chartRaw f v w := by
  intro u w c h
  classical
  dsimp [chartRaw]
  have hc : c ≠ 0 := by intro hc; apply u.2; rw [h, hc, zero_smul]
  by_cases hu : f (u : V) = 0
  · have hw : f (w : V) = 0 := by
      have hmul : c * f (w : V) = 0 := by simpa [h, map_smul, smul_eq_mul] using hu
      exact (mul_eq_zero.mp hmul).resolve_left hc
    rw [if_pos hu, if_pos hw]
  · have hw : f (w : V) ≠ 0 := by intro hw; apply hu; simp [h, map_smul, smul_eq_mul, hw]
    rw [if_neg hu, if_neg hw, h, sub_left_inj, map_smul, smul_eq_mul, smul_smul]
    have hsc : ((c * f (w : V))⁻¹ * c) = (f (w : V))⁻¹ := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [hsc]

omit [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] [ContinuousSMul K V]
    [IsTopologicalDivisionRing K] [T1Space K] in
/-- The `chartRaw` representative always lies in `ker f` after normalization by `hv`. -/
theorem chartRaw_mem_ker (f : V →L[K] K) (v : V) (hv : f v = 1) (x : ℙ K V) :
    f (x.lift (chartRaw f v) (chartRaw_wd f v)) = 0 := by
  classical
  induction x using Quotient.inductionOn'
  case h u =>
    change f (chartRaw f v u) = 0
    by_cases hu : f (u : V) = 0 <;> simp [chartRaw, hu, hv]

/-- Forward map of the affine chart. -/
noncomputable def chartToFun (f : V →L[K] K) (v : V) (hv : f v = 1) : ℙ K V → f.ker :=
  fun x => ⟨x.lift (chartRaw f v) (chartRaw_wd f v), chartRaw_mem_ker f v hv x⟩

/-- Inverse map of the affine chart. -/
def chartInvFun (f : V →L[K] K) (v : V) (hv : f v = 1) : f.ker → ℙ K V :=
  fun w => mk' K ⟨w.1 + v, by
    have hne : f (w.1 + v) ≠ 0 := by simp [map_add, hv]
    intro hwv
    exact hne (by simp [hwv])⟩

/-- The affine chart defined by a linear functional `f` and a vector `v` with `f v = 1`. -/
def affineChart (f : V →L[K] K) (v : V) (hv : f v = 1) : OpenPartialHomeomorph (ℙ K V) (f.ker) where
  source := affineChartDomain f
  target := Set.univ
  toFun := chartToFun f v hv
  invFun := chartInvFun f v hv
  map_source' := fun x hx ↦ trivial
  map_target' := fun w _ ↦ by
    simp only [affineChartDomain, Set.mem_image, Set.mem_setOf_eq, Subtype.exists]
    have hfw : f (w.1 + v) ≠ 0 := by simp [map_add, hv]
    exact ⟨w.1 + v, (fun hwv ↦ hfw (by simp [hwv])), hfw, rfl⟩
  left_inv' := fun x hx ↦ by
    simp only [affineChartDomain, Set.mem_image, Set.mem_setOf_eq, Subtype.exists] at hx
    rcases hx with ⟨u, hu0, hfu, rfl⟩
    rw [chartInvFun, chartToFun]
    simp only [Projectivization.lift_mk, mk'_eq_mk, chartRaw, if_neg hfu]
    rw [mk_eq_mk_iff]
    refine ⟨(Units.mk0 (f u) hfu)⁻¹, ?_⟩
    simp [Units.smul_def]
  right_inv' := fun w _ ↦ by
    ext
    rw [chartInvFun, chartToFun]
    simp [Projectivization.lift_mk, chartRaw, map_add, hv, mk'_eq_mk]
  open_source := isOpen_affineChartDomain f
  open_target := isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_open_iff (isOpen_affineChartDomain f)]
    intro U hU
    rw [isOpen_coinduced]
    have h_open_dom : IsOpen {u : {x : V // x ≠ 0} | f u ≠ 0} := by
      have h_cont : Continuous fun u : {x : V // x ≠ 0} => f u :=
        f.continuous.comp continuous_subtype_val
      exact (isClosed_singleton.preimage h_cont).isOpen_compl
    have h_cont_chart :
        ContinuousOn (fun u : {x : V // x ≠ 0} => chartToFun f v hv (mk' K u)) {u | f u ≠ 0} := by
      rw [continuousOn_iff_continuous_restrict]
      let s : Set {x : V // x ≠ 0} := {u | f u ≠ 0}
      change Continuous (fun u : s => chartToFun f v hv (mk' K u.1))
      let g : s → f.ker := fun u =>
        ⟨(f u.1)⁻¹ • (u.1 : V) - v, by
          change f ((f u.1)⁻¹ • (u.1 : V) - v) = 0
          rw [map_sub, map_smul, smul_eq_mul, hv, inv_mul_cancel₀ u.2, sub_self]⟩
      have hg : Continuous g := by
        exact
          ((Continuous.inv₀
              (f.continuous.comp (continuous_subtype_val.comp continuous_subtype_val))
              (fun u : s => u.2)).smul
            (continuous_subtype_val.comp continuous_subtype_val)).sub continuous_const |>.subtype_mk
            (fun u => by
              change f ((f u.1)⁻¹ • (u.1 : V) - v) = 0
              rw [map_sub, map_smul, smul_eq_mul, hv, inv_mul_cancel₀ u.2, sub_self])
      have h_eq : (fun u : s => chartToFun f v hv (mk' K u.1)) = g := by
        funext u
        ext
        have hu : f (u.1 : V) ≠ 0 := u.2
        simp [g, chartToFun, Projectivization.lift_mk, chartRaw, hu]
      simpa [g] using h_eq ▸ hg
    have h_match :
        mk' K ⁻¹' (affineChartDomain f ∩ (chartToFun f v hv) ⁻¹' U) =
          {u : {x : V // x ≠ 0} | f u ≠ 0} ∩
            (fun u : {x : V // x ≠ 0} => chartToFun f v hv (mk' K u)) ⁻¹' U := by
      ext u
      change
        (mk' K u ∈ affineChartDomain f ∧ chartToFun f v hv (mk' K u) ∈ U) ↔
          (f u ≠ 0 ∧ chartToFun f v hv (mk' K u) ∈ U)
      exact and_congr (mk'_mem_affineChartDomain_iff f u) Iff.rfl
    change IsOpen (mk' K ⁻¹' (affineChartDomain f ∩ (chartToFun f v hv) ⁻¹' U))
    rw [h_match]
    exact h_cont_chart.isOpen_inter_preimage h_open_dom hU
  continuousOn_invFun := by
    apply Continuous.continuousOn
    refine (continuous_coinduced_rng (f := (mk' K : {x : V // x ≠ 0} → ℙ K V))).comp ?_
    exact (continuous_subtype_val.add continuous_const).subtype_mk _

/-- Local alias for `_root_.SeparatingDual`, specialized to this file's notation. -/
abbrev SeparatingDual : Prop := ∀ v : V, v ≠ 0 → ∃ f : V →L[K] K, f v ≠ 0

omit [ContinuousAdd V] [ContinuousNeg V] [ContinuousSub V] [ContinuousSMul K V]
    [IsTopologicalDivisionRing K] [T1Space K] in
/-- The dual separates points iff affine-chart domains cover projective space. -/
theorem separatingDual_iff_range :
    SeparatingDual (K := K) (V := V) ↔
      (⋃ f : V →L[K] K, affineChartDomain (K := K) f) = Set.univ := by
  constructor
  · intro h
    rw [Set.eq_univ_iff_forall]
    intro x
    induction x using Quotient.inductionOn' with
    | h v =>
      rcases h v v.2 with ⟨f, hf⟩
      exact Set.mem_iUnion.2 ⟨f, ⟨v, hf, rfl⟩⟩
  · intro h v hv
    have : mk' K ⟨v, hv⟩ ∈ ⋃ f : V →L[K] K, affineChartDomain f := by simp [h]
    simp only [Set.mem_iUnion, affineChartDomain, Set.mem_image, Set.mem_setOf_eq] at this
    rcases this with ⟨f, u, hfu, hua⟩
    rw [mk'_eq_mk, mk'_eq_mk, mk_eq_mk_iff] at hua
    rcases hua with ⟨c, hc⟩
    use f
    rw [← hc] at hfu
    change f ((c : K) • v) ≠ 0 at hfu
    rw [map_smul, smul_eq_mul] at hfu
    exact fun hfv ↦ hfu (by simp [hfv])

section Normed

variable {𝕜 : Type*} {W : Type*} {F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A fixed model space for affine charts on projective space.

For every normalized pair `(f, v)` with `f v = 1`, this provides a continuous
linear equivalence `f.ker ≃L[𝕜] F`. -/
class HyperplaneModel (𝕜 W F : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] where
  equiv : ∀ (f : W →L[𝕜] 𝕜) (v : W), f v = 1 → f.ker ≃L[𝕜] F

variable [HyperplaneModel 𝕜 W F]

/-- Affine chart with codomain transported to a fixed model space `F`. -/
noncomputable def affineChartModel (f : W →L[𝕜] 𝕜) (v : W) (hv : f v = 1) :
    OpenPartialHomeomorph (ℙ 𝕜 W) F :=
  (affineChart f v hv).transHomeomorph
    ((HyperplaneModel.equiv f v hv).toHomeomorph)

/-- The source of `affineChartModel` is definitionally `affineChartDomain`. -/
@[simp]
theorem affineChartModel_source (f : W →L[𝕜] 𝕜) (v : W) (hv : f v = 1) :
    (affineChartModel (F := F) f v hv).source = affineChartDomain f := rfl

/-- Atlas generated by affine charts transported to a fixed model space `F`. -/
noncomputable def affineAtlasModel : Set (OpenPartialHomeomorph (ℙ 𝕜 W) F) :=
  {e | ∃ (f : W →L[𝕜] 𝕜) (v : W) (hv : f v = 1), e = affineChartModel f v hv}

/-- Linear part of the inverse chart map `(f, v, hv)`, before translating by `v`. -/
noncomputable def preimageCLM (f : W →L[𝕜] 𝕜) (v : W) (hv : f v = 1) : F →L[𝕜] W :=
  (f.ker.subtypeL).comp ((HyperplaneModel.equiv f v hv).symm.toContinuousLinearMap)

/-- Affine lift of `preimageCLM`, i.e. the inverse-chart representative in `W`. -/
noncomputable def preimageVec (f : W →L[𝕜] 𝕜) (v : W) (hv : f v = 1) (x : F) : W :=
  preimageCLM f v hv x + v

/-- Projection to `g.ker` along the direction `w`, assuming `g w = 1`. -/
noncomputable def toKerCLM (g : W →L[𝕜] 𝕜) (w : W) (hw : g w = 1) : W →L[𝕜] g.ker where
  toLinearMap :=
    { toFun := fun y => ⟨y - g y • w, by simp [map_sub, map_smul, hw]⟩
      map_add' := by intro x y; ext; simp [sub_eq_add_neg, add_smul, add_assoc, add_left_comm,
        add_comm]
      map_smul' := by intro c y; ext; simp [smul_sub, mul_smul] }
  cont := Continuous.subtype_mk ((ContinuousLinearMap.id 𝕜 W).continuous.sub
    ((g.smulRight w).continuous)) (by intro y; simp [map_sub, map_smul, hw])

/-- Explicit formula for change of affine charts in model coordinates. -/
noncomputable def transitionMap
    (f g : W →L[𝕜] 𝕜) (v w : W) (hv : f v = 1) (hw : g w = 1) (x : F) : F :=
  ((HyperplaneModel.equiv g w hw).toContinuousLinearMap.comp
    (toKerCLM g w hw)) (((g (preimageVec f v hv x))⁻¹) • preimageVec f v hv x)

/-- Source of `transitionMap`: points where the normalization denominator is nonzero. -/
noncomputable def transitionSource (f g : W →L[𝕜] 𝕜) (v : W) (hv : f v = 1) : Set F :=
  {x | g (preimageVec f v hv x) ≠ 0}

/-- The source of the chart transition equals `transitionSource`. -/
theorem mem_transition_source_iff
    (f g : W →L[𝕜] 𝕜) (v w : W) (hv : f v = 1) (hw : g w = 1) (x : F) :
      x ∈ ((affineChartModel f v hv).symm.trans (affineChartModel (F := F) g w hw)).source ↔
      x ∈ transitionSource f g v hv := by
  constructor
  · intro hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    rcases hx with ⟨_, hx2⟩
    have hu : ↑((HyperplaneModel.equiv f v hv).symm x) + v ≠ 0 := by
      intro hzero
      have hker : f ↑((HyperplaneModel.equiv f v hv).symm x) = 0 :=
        ((HyperplaneModel.equiv f v hv).symm x).2
      have : (1 : 𝕜) = 0 := by
        calc
          (1 : 𝕜) = f (↑((HyperplaneModel.equiv f v hv).symm x) + v) := by simp [map_add, hker, hv]
          _ = 0 := by simp [hzero]
      exact one_ne_zero this
    change (affineChartModel f v hv).symm x ∈ affineChartDomain g at hx2
    change chartInvFun f v hv ((HyperplaneModel.equiv f v hv).symm x) ∈ affineChartDomain g at hx2
    have hx3 : mk 𝕜 (↑((HyperplaneModel.equiv f v hv).symm x) + v) hu ∈ affineChartDomain g := by
      simpa [chartInvFun, mk'_eq_mk] using hx2
    simpa [transitionSource, preimageVec, preimageCLM, map_add]
      using (mk_mem_affineChartDomain_iff g _ hu).1 hx3
  · intro hx
    have hx' : g (↑((HyperplaneModel.equiv f v hv).symm x) + v) ≠ 0 := by
      simpa [transitionSource, preimageVec, preimageCLM, map_add] using hx
    have hu : ↑((HyperplaneModel.equiv f v hv).symm x) + v ≠ 0 := by
      intro hzero
      exact hx' (by simp [hzero])
    have hx2 : mk 𝕜 (↑((HyperplaneModel.equiv f v hv).symm x) + v) hu ∈ affineChartDomain g :=
      (mk_mem_affineChartDomain_iff g _ hu).2 hx'
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨by trivial, ?_⟩
    change (affineChartModel f v hv).symm x ∈ affineChartDomain g
    change chartInvFun f v hv ((HyperplaneModel.equiv f v hv).symm x) ∈ affineChartDomain g
    simpa [chartInvFun, mk'_eq_mk] using hx2

/-- The transition map in model coordinates is analytic on its source. -/
theorem contDiffOn_transitionMap
    (f g : W →L[𝕜] 𝕜) (v w : W) (hv : f v = 1) (hw : g w = 1) :
    ContDiffOn 𝕜 ω (transitionMap f g v w hv hw) (transitionSource (F := F) f g v hv) := by
  let u : F → W := preimageVec f v hv
  have hu : ContDiff 𝕜 ω u := by simpa [u, preimageVec] using
    ((preimageCLM f v hv).contDiff.add contDiff_const)
  have hg_u : ContDiff 𝕜 ω (fun x : F => g (u x)) := g.contDiff.comp hu
  have hginv : ContDiffOn 𝕜 ω (fun x : F => (g (u x))⁻¹) (transitionSource f g v hv) := by
    refine hg_u.contDiffOn.inv ?_
    intro x hx
    exact hx
  have hsmul : ContDiffOn 𝕜 ω (fun x : F => (g (u x))⁻¹ • u x) (transitionSource f g v hv) :=
    hginv.smul hu.contDiffOn
  have hlin : ContDiffOn 𝕜 ω ((HyperplaneModel.equiv (F := F) g w hw).toContinuousLinearMap.comp
    (toKerCLM g w hw)) Set.univ := by
    simpa using ((HyperplaneModel.equiv g w hw).toContinuousLinearMap.comp
      (toKerCLM g w hw)).contDiff.contDiffOn
  simpa [transitionMap, transitionSource, u, Function.comp] using hlin.comp hsmul (by
    intro x hx; trivial)

/-- On `transitionSource`, the chart transition equals `transitionMap`. -/
theorem transition_eq_on_source
    (f g : W →L[𝕜] 𝕜) (v w : W) (hv : f v = 1) (hw : g w = 1) (x : F)
      (hx : x ∈ transitionSource f g v hv) :
  ((affineChartModel f v hv).symm.trans (affineChartModel g w hw)) x =
    transitionMap f g v w hv hw x := by
  let y : W := ↑((HyperplaneModel.equiv f v hv).symm x)
  let d : 𝕜 := g y + g v
  have hne' : d ≠ 0 := by
    have hne : g (preimageVec f v hv x) ≠ 0 := hx
    simpa [preimageVec, preimageCLM, y, d, map_add] using hne
  have hs' : d⁻¹ * g y + d⁻¹ * g v = (1 : 𝕜) := by
    calc
      d⁻¹ * g y + d⁻¹ * g v = d⁻¹ * (g y + g v) := by rw [mul_add]
      _ = 1 := by simp [d, hne']
  simp only [affineChartModel, affineChart, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.transHomeomorph_apply, OpenPartialHomeomorph.mk_coe,
    OpenPartialHomeomorph.transHomeomorph_symm_apply, OpenPartialHomeomorph.mk_coe_symm,
    PartialEquiv.coe_symm_mk, ContinuousLinearEquiv.coe_symm_toHomeomorph, Function.comp_apply,
    chartInvFun, mk'_eq_mk, chartToFun, Projectivization.lift_mk, chartRaw, map_add, smul_add,
    transitionMap, preimageVec, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    map_smul, y, d, hne']
  rw [← (HyperplaneModel.equiv g w hw).map_smul, ← (HyperplaneModel.equiv g w hw).map_smul,
    ← (HyperplaneModel.equiv g w hw).map_add]
  refine congrArg (HyperplaneModel.equiv g w hw) ?_
  ext
  change
    d⁻¹ • y + d⁻¹ • v - w =
      d⁻¹ • (((toKerCLM g w hw) y : g.ker) : W) + d⁻¹ • (((toKerCLM g w hw) v : g.ker) : W)
  have hcalc :
      -w + (d⁻¹ • v + d⁻¹ • y) =
        d⁻¹ • v + (d⁻¹ • y + (-((d⁻¹ * g v) • w) + -((d⁻¹ * g y) • w))) := by
    have hs'' : d⁻¹ * g v + d⁻¹ * g y = (1 : 𝕜) := by simpa [add_comm] using hs'
    calc
    -w + (d⁻¹ • v + d⁻¹ • y) = d⁻¹ • v + (d⁻¹ • y - w) := by
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = d⁻¹ • v + (d⁻¹ • y - ((d⁻¹ * g v + d⁻¹ * g y) • w)) := by
      have hone : w = (d⁻¹ * g v + d⁻¹ * g y) • w := by simp [hs'']
      exact congrArg (fun z : W => d⁻¹ • v + (d⁻¹ • y - z)) hone
    _ = d⁻¹ • v + (d⁻¹ • y + (-((d⁻¹ * g v) • w) + -((d⁻¹ * g y) • w))) := by
      simp [sub_eq_add_neg, add_smul, mul_smul, add_comm]
  calc
    d⁻¹ • y + d⁻¹ • v - w = -w + (d⁻¹ • v + d⁻¹ • y) := by simp [sub_eq_add_neg, add_comm]
    _ = d⁻¹ • v + (d⁻¹ • y + (-((d⁻¹ * g v) • w) + -((d⁻¹ * g y) • w))) := hcalc
    _ = d⁻¹ • (((toKerCLM g w hw) y : g.ker) : W) + d⁻¹ • (((toKerCLM g w hw) v : g.ker) : W) := by
        have hy : (((toKerCLM g w hw) y : g.ker) : W) = y - g y • w := rfl
        have hv : (((toKerCLM g w hw) v : g.ker) : W) = v - g v • w := rfl
        rw [hy, hv, smul_sub, smul_sub, mul_smul, mul_smul, sub_eq_add_neg, sub_eq_add_neg]
        ac_rfl

/-- The transition between two model affine charts is analytic on its source. -/
theorem contDiffOn_affineChartModel_transition
    (f g : W →L[𝕜] 𝕜) (v w : W) (hv : f v = 1) (hw : g w = 1) :
  ContDiffOn 𝕜 ω (fun x => ((affineChartModel (F := F) f v hv).symm.trans
    (affineChartModel (F := F) g w hw)) x) (((affineChartModel (F := F) f v hv).symm.trans
    (affineChartModel (F := F) g w hw)).source) := by
  have hmap := contDiffOn_transitionMap (F := F) f g v w hv hw
  have hsrc : ((affineChartModel (F := F) f v hv).symm.trans
    (affineChartModel (F := F) g w hw)).source = transitionSource f g v hv := by
    ext x
    exact mem_transition_source_iff f g v w hv hw x
  refine hsrc.symm ▸ ?_
  refine hmap.congr ?_
  intro x hx
  exact transition_eq_on_source f g v w hv hw x hx

variable [_root_.SeparatingDual 𝕜 W]

/-- Every point of projective space belongs to the source of some chart in `affineAtlasModel`. -/
theorem exists_chart_mem_affineAtlasModel_and_source (x : ℙ 𝕜 W) :
    ∃ e ∈ affineAtlasModel (F := F), x ∈ e.source := by
  induction x using Quotient.inductionOn' with
  | h u =>
      rcases _root_.SeparatingDual.exists_eq_one (R := 𝕜) (V := W) u.2 with ⟨f, hf⟩
      refine ⟨affineChartModel f u hf, ?_, ?_⟩
      · exact ⟨f, u, hf, rfl⟩
      · change mk' 𝕜 u ∈ affineChartDomain f
        exact ⟨u, by simp [hf], rfl⟩

/-- A preferred affine chart (with codomain `F`) at each point of projective space. -/
noncomputable def chartAtModel (x : ℙ 𝕜 W) : OpenPartialHomeomorph (ℙ 𝕜 W) F :=
  Classical.choose (exists_chart_mem_affineAtlasModel_and_source x)

/-- Charted space structure on projective space, with model `F`,
assuming a separating dual and a fixed model for all affine-chart hyperplanes. -/
noncomputable instance instChartedSpaceProjectiveSpace :
    ChartedSpace F (ℙ 𝕜 W) where
  atlas := affineAtlasModel (F := F)
  chartAt := chartAtModel (F := F)
  mem_chart_source x := (Classical.choose_spec (exists_chart_mem_affineAtlasModel_and_source x)).2
  chart_mem_atlas x := (Classical.choose_spec (exists_chart_mem_affineAtlasModel_and_source x)).1

/-- With this atlas, projective space is an analytic manifold over `F`. -/
instance instIsManifoldAnalyticProjectiveSpace : IsManifold (modelWithCornersSelf 𝕜 F) ω (ℙ 𝕜 W) :=
  isManifold_of_contDiffOn (modelWithCornersSelf 𝕜 F) ω (ℙ 𝕜 W) (by
    rintro e e' ⟨f, v, hv, rfl⟩ ⟨g, w, hw, rfl⟩
    simpa [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.univ_inter, Set.inter_univ]
      using contDiffOn_affineChartModel_transition f g v w hv hw)

end Normed

end Projectivization
