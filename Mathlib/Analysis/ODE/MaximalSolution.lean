/-
Copyright (c) 2025 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Zorn
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Maximal Solutions to Ordinary Differential Equations

This file defines the concept of a maximal solution to an ODE `x' = v(t, x)` with initial
condition `x(t₀) = x₀`. It proves that under the conditions of the Picard-Lindelöf theorem,
such a maximal solution exists. Some auxiliary structures (e.g. `LocalODESolution`) are
introduced only for the Zorn's Lemma proof and are not intended for public use.

The strategy involves using Zorn's Lemma on the set of all local ODE solutions, ordered by
extension. Picard-Lindelöf's theorem provides the existence of at least one local solution,
ensuring the set is non-empty. The core of the Zorn's Lemma application is showing that
every chain of solutions has an upper bound, constructed by "gluing" the solutions in the
chain together.

## Main Definitions

* `IsMaximalODESolution`: Predicate stating that an integral curve `(f, I)` cannot be extended
  to a solution on any strictly larger open connected domain.

## Main Theorem

* `exists_maximal_ode_solution`: Under Picard-Lindelöf conditions (ensuring local existence
  on an open interval around `t₀`), there exists a function `f` and an open connected set `I`
  (an open interval) such that `(f, I)` is a maximal solution.

## TODO

* Implement the compact exit lemma ("lemme des bouts").
-/

@[expose] public section

open Set Filter NNReal Topology TopologicalSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (v : ℝ → E → E) (t₀ : ℝ) (x₀ : E)

/--
If two solutions `f₁` and `f₂` to the ODE `y' = v(t,y)` pass through the same point `(t₀, x₀)`,
and `v(t,·)` is Lipschitz continuous with a uniform constant `K` for `x ∈ univ E`
for all `t` in the intersection of their domains `I₁ ∩ I₂`, then `f₁` and `f₂` agree on this
entire intersection. This is a standard uniqueness result derived from Gronwall's inequality.
-/
lemma IsIntegralCurveOn.eqOn_of_agree_at_t₀_of_lipschitz
    {f₁ f₂ : ℝ → E} {I₁ I₂ : Set ℝ}
    (h₁ : IsIntegralCurveOn f₁ v I₁)
    (h₂ : IsIntegralCurveOn f₂ v I₂)
    (h₁_open : IsOpen I₁) (h₂_open : IsOpen I₂)
    (h₁_conn : IsConnected I₁) (h₂_conn : IsConnected I₂)
    (ht₀₁ : t₀ ∈ I₁) (ht₀₂ : t₀ ∈ I₂)
    (heq_at_t₀ : f₁ t₀ = f₂ t₀)
    {K : ℝ≥0} (h_lipschitz : ∀ t ∈ I₁ ∩ I₂, LipschitzWith K (v t)) :
    EqOn f₁ f₂ (I₁ ∩ I₂) := by
  let K_int := I₁ ∩ I₂
  have hK_int_ord : OrdConnected K_int := by simpa [K_int] using
    (h₁_conn.isPreconnected.ordConnected).inter (h₂_conn.isPreconnected.ordConnected)
  intro t' ht'_in_K_int
  rcases le_total t₀ t' with h_t₀_le_t' | h_t'_le_t₀
  · -- Forward-time case: apply uniqueness on `[t₀, t']`.
    have hJ_sub_K_int : Icc t₀ t' ⊆ K_int := by
      intro j hj_in_J
      exact hK_int_ord.out (show t₀ ∈ K_int from ⟨ht₀₁, ht₀₂⟩) ht'_in_K_int hj_in_J
    have hv_J : ∀ t ∈ Ico t₀ t', LipschitzOnWith K (v t) univ := by
      intro t ht_in_Ico
      exact (h_lipschitz t (hJ_sub_K_int (mem_Icc_of_Ico ht_in_Ico))).lipschitzOnWith
    have hf₁_cont_J : ContinuousOn f₁ (Icc t₀ t') :=
      (h₁.continuousOn).mono (hJ_sub_K_int.trans inter_subset_left)
    have hf₁'_deriv_J : ∀ t ∈ Ico t₀ t', HasDerivWithinAt f₁ (v t (f₁ t)) (Ici t) t := by
      intro t ht_in_Ico
      have ht_in_I₁ := hJ_sub_K_int.trans inter_subset_left (mem_Icc_of_Ico ht_in_Ico)
      exact ((h₁ t ht_in_I₁).hasDerivAt (h₁_open.mem_nhds ht_in_I₁)).hasDerivWithinAt
    have hf₂_cont_J : ContinuousOn f₂ (Icc t₀ t') :=
      (h₂.continuousOn).mono (hJ_sub_K_int.trans inter_subset_right)
    have hf₂'_deriv_J : ∀ t ∈ Ico t₀ t', HasDerivWithinAt f₂ (v t (f₂ t)) (Ici t) t := by
      intro t ht_in_Ico
      have ht_in_I₂ := hJ_sub_K_int.trans inter_subset_right (mem_Icc_of_Ico ht_in_Ico)
      exact ((h₂ t ht_in_I₂).hasDerivAt (h₂_open.mem_nhds ht_in_I₂)).hasDerivWithinAt
    exact (ODE_solution_unique_of_mem_Icc_right hv_J hf₁_cont_J hf₁'_deriv_J (by simp)
        hf₂_cont_J hf₂'_deriv_J (by simp) heq_at_t₀) (right_mem_Icc.mpr h_t₀_le_t')
  · -- Backward-time case: apply uniqueness on `[t', t₀]`.
    have hJ_sub_K_int : Icc t' t₀ ⊆ K_int := by
      intro j hj_in_J
      exact hK_int_ord.out ht'_in_K_int (show t₀ ∈ K_int from ⟨ht₀₁, ht₀₂⟩) hj_in_J
    have hv_J : ∀ t ∈ Ioc t' t₀, LipschitzOnWith K (v t) univ := by
      intro t ht_in_Ioc
      exact (h_lipschitz t (hJ_sub_K_int (mem_Icc_of_Ioc ht_in_Ioc))).lipschitzOnWith
    have hf₁_cont_J : ContinuousOn f₁ (Icc t' t₀) :=
      (h₁.continuousOn).mono (hJ_sub_K_int.trans inter_subset_left)
    have hf₁'_deriv_J : ∀ t ∈ Ioc t' t₀, HasDerivWithinAt f₁ (v t (f₁ t)) (Iic t) t := by
      intro t ht_in_Ioc
      have ht_in_I₁ := hJ_sub_K_int.trans inter_subset_left (mem_Icc_of_Ioc ht_in_Ioc)
      exact ((h₁ t ht_in_I₁).hasDerivAt (h₁_open.mem_nhds ht_in_I₁)).hasDerivWithinAt
    have hf₂_cont_J : ContinuousOn f₂ (Icc t' t₀) :=
      (h₂.continuousOn).mono (hJ_sub_K_int.trans inter_subset_right)
    have hf₂'_deriv_J : ∀ t ∈ Ioc t' t₀, HasDerivWithinAt f₂ (v t (f₂ t)) (Iic t) t := by
      intro t ht_in_Ioc
      have ht_in_I₂ := hJ_sub_K_int.trans inter_subset_right (mem_Icc_of_Ioc ht_in_Ioc)
      exact ((h₂ t ht_in_I₂).hasDerivAt (h₂_open.mem_nhds ht_in_I₂)).hasDerivWithinAt
    exact (ODE_solution_unique_of_mem_Icc_left hv_J hf₁_cont_J hf₁'_deriv_J (by simp)
        hf₂_cont_J hf₂'_deriv_J (by simp) heq_at_t₀) (left_mem_Icc.mpr h_t'_le_t₀)

/--
A solution `(f, I)` to the ODE `x' = v(t, x)` is maximal if it cannot be extended to a solution
on any strictly larger open connected domain `J`. Initial conditions are added as separate
hypotheses in the theorems below.
-/
structure IsMaximalODESolution (v : ℝ → E → E) (f : ℝ → E) (I : Set ℝ) : Prop where
  /-- The domain `I` must be an open set. -/
  isOpen_domain : IsOpen I
  /-- The domain `I` must be connected. -/
  isConnected_domain : IsConnected I
  /-- The function `f` must have the derivative `v t (f t)` at every point `t` in `I`. -/
  isIntegralCurveOn : IsIntegralCurveOn f v I
  /-- The maximality condition: If `(g, J)` is another solution such that `I ⊆ J` and `f` agrees
  with `g` on `I`, then `I` must be equal to `J`. -/
  is_maximal : ∀ {g : ℝ → E} {J : Set ℝ}, IsIntegralCurveOn g v J → IsOpen J → IsConnected J →
    I ⊆ J → (EqOn f g I) → I = J

/--
Domain-restricted maximal ODE solutions.

`IsMaximalODESolutionWithin U v f I` stores maximality for the zero-extension of `v` outside `U`,
and separately records that the trajectory stays in `U` on `I`.
-/
structure IsMaximalODESolutionWithin (U : Set (ℝ × E))
    (v : {p : ℝ × E // p ∈ U} → E) (f : ℝ → E) (I : Set ℝ) : Prop where
  toIsMaximal : IsMaximalODESolution (extendVectorField U v) f I
  mapsTo : ∀ t ∈ I, (t, f t) ∈ U

namespace IsMaximalODESolutionWithin

variable {U : Set (ℝ × E)} {v : {p : ℝ × E // p ∈ U} → E} {f : ℝ → E} {I : Set ℝ}

lemma isOpen_domain (h : IsMaximalODESolutionWithin U v f I) : IsOpen I :=
  h.toIsMaximal.isOpen_domain

lemma isConnected_domain (h : IsMaximalODESolutionWithin U v f I) : IsConnected I :=
  h.toIsMaximal.isConnected_domain

lemma isIntegralCurveOn
    (h : IsMaximalODESolutionWithin U v f I) :
    IsIntegralCurveOnWithin f U v I :=
  ⟨h.mapsTo, h.toIsMaximal.isIntegralCurveOn⟩

/-- Specialization of `IsMaximalODESolutionWithin` to `U = univ`.

When the domain constraint is the whole space, the `Within` notion is equivalent to the usual
notion of maximal ODE solution. -/
theorem univ_iff {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ} :
    IsMaximalODESolutionWithin
        (U := (Set.univ : Set (ℝ × E)))
        (v := fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => v p.1.1 p.1.2)
        f I ↔
      IsMaximalODESolution v f I := by
  classical
  have hExt :
      extendVectorField (U := (Set.univ : Set (ℝ × E)))
          (fun p : {p : ℝ × E // p ∈ (Set.univ : Set (ℝ × E))} => v p.1.1 p.1.2) = v := by
    funext t x
    simp [extendVectorField]
  constructor
  · intro h
    simpa [hExt] using h.toIsMaximal
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [hExt] using h
    · intro t ht
      simp

end IsMaximalODESolutionWithin

section TimeReversalHelpers

variable {v : ℝ → E → E} {f : ℝ → E} {I : Set ℝ}

theorem IsMaximalODESolution.comp_neg_iff :
    IsMaximalODESolution (fun t x ↦ - v (-t) x) (f ∘ Neg.neg) (Neg.neg ⁻¹' I) ↔
    IsMaximalODESolution v f I := by
  constructor
  · intro h
    refine ⟨?_, ?_, IsIntegralCurveOn.comp_neg_iff.mp h.isIntegralCurveOn, ?_⟩
    · simpa [preimage_neg_neg_set] using h.isOpen_domain.preimage continuous_neg
    · exact ((Homeomorph.neg ℝ).isConnected_preimage (s:=I)).1 h.isConnected_domain
    intro g J hg hJopen hJconn hIJ hEq
    have h_rev := h.isMaximal (g ∘ Neg.neg) (Neg.neg ⁻¹' J)
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
    refine ⟨?_, ?_, IsIntegralCurveOn.comp_neg_iff.mpr h.isIntegralCurveOn, ?_⟩
    · simpa [preimage_neg_neg_set] using h.isOpen_domain.preimage continuous_neg
    · exact ((Homeomorph.neg ℝ).isConnected_preimage (s:=I)).2 h.isConnected_domain
    intro g J hg hJopen hJconn hIJ hEq
    have hg' : IsIntegralCurveOn (g ∘ Neg.neg) v (Neg.neg ⁻¹' J) := by
      have hg' :=
        (IsIntegralCurveOn.comp_neg_iff (v:=fun t x ↦ - v (-t) x) (γ:=g) (s:=J)).mpr hg
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
    have h_rev := h.isMaximal (g ∘ Neg.neg) (Neg.neg ⁻¹' J)
      hg'
      (hJopen.preimage continuous_neg)
      (((Homeomorph.neg ℝ).isConnected_preimage (s:=J)).2 hJconn)
      hIJ'
      hEq'
    have h_rev' := congrArg (fun s => Neg.neg ⁻¹' s) h_rev
    simpa [preimage_neg_neg_set] using h_rev'

end TimeReversalHelpers

open Classical in
/--
If `h_loc` is any local solution to the ODE and `h_max` is a maximal solution,
then the domain of `h_loc` is a subset of the domain of `h_max`. This relies on the
uniqueness of solutions on the intersection of their domains, guaranteed by Lipschitz
conditions on `v`.
-/
lemma IsIntegralCurveOn.subset_maximal_domain_with_lipschitz
    {f_loc : ℝ → E} {I_loc : Set ℝ} (h_loc : IsIntegralCurveOn f_loc v I_loc)
    (h_loc_open : IsOpen I_loc) (h_loc_conn : IsConnected I_loc)
    (ht₀_loc : t₀ ∈ I_loc) (hf_loc_t₀ : f_loc t₀ = x₀)
    {f_max : ℝ → E} {I_max : Set ℝ} (h_max : IsMaximalODESolution v f_max I_max)
    (ht₀_max : t₀ ∈ I_max) (hf_max_t₀ : f_max t₀ = x₀)
    {K : ℝ≥0} (h_v_lipschitz : ∀ t ∈ I_loc ∩ I_max, LipschitzWith K (v t)) :
    I_loc ⊆ I_max := by
  -- First show the two solutions agree on `I_loc ∩ I_max` by uniqueness.
  have h_agree_on_inter : EqOn f_loc f_max (I_loc ∩ I_max) :=
    IsIntegralCurveOn.eqOn_of_agree_at_t₀_of_lipschitz v t₀ h_loc
      h_max.isIntegralCurveOn h_loc_open h_max.isOpen_domain h_loc_conn h_max.isConnected_domain
      ht₀_loc ht₀_max (by simp [hf_loc_t₀, hf_max_t₀]) h_v_lipschitz
  -- Glue the two solutions along the overlap.
  let f_union (t : ℝ) : E := if t ∈ I_max then f_max t else f_loc t
  -- Show the glued function is still a solution on `I_loc ∪ I_max`.
  have h_union_conn : IsConnected (I_loc ∪ I_max) := by
    exact IsConnected.union ⟨t₀, ⟨ht₀_loc, ht₀_max⟩⟩ h_loc_conn h_max.isConnected_domain
  have h_union_sol : IsIntegralCurveOn f_union v (I_loc ∪ I_max) := by
    intro t ht_in_union
    if ht_in_I_max : t ∈ I_max then
      -- On `I_max`, `f_union` is locally equal to `f_max`.
      have h_fmax_deriv : HasDerivAt f_max (v t (f_max t)) t :=
        (h_max.isIntegralCurveOn t ht_in_I_max).hasDerivAt
          (h_max.isOpen_domain.mem_nhds ht_in_I_max)
      have heq_eventually : f_union =ᶠ[𝓝 t] f_max := by
        filter_upwards [h_max.isOpen_domain.mem_nhds ht_in_I_max] with y hy_in_Imax
        simp [hy_in_Imax, f_union]
      rw [show f_union t = f_max t by simp [f_union, ht_in_I_max]]
      exact (HasDerivAt.congr_of_eventuallyEq h_fmax_deriv heq_eventually).hasDerivWithinAt
    else
      -- Off `I_max`, write `f_union = f_loc + φ` where `φ` has zero derivative at `t`.
      have ht_in_I_loc : t ∈ I_loc := ht_in_union.resolve_right ht_in_I_max
      have h_floc_deriv : HasDerivAt f_loc (v t (f_loc t)) t :=
        (h_loc t ht_in_I_loc).hasDerivAt (h_loc_open.mem_nhds ht_in_I_loc)
      let φ y := if y ∈ I_max then f_max y - f_loc y else (0:E)
      have h_phi_t_is_zero : φ t = 0 := by simp [φ, ht_in_I_max]
      have h_phi_deriv_zero : HasDerivAt φ (0:E) t := by
        apply hasDerivAtFilter_iff_tendsto_slope.mpr
        have h_slope_eventually_zero : ∀ᶠ y in 𝓝[≠] t, slope φ t y = (0:E) := by
          have I_loc_mem_nhds_t : I_loc ∈ 𝓝 t := h_loc_open.mem_nhds ht_in_I_loc
          filter_upwards [diff_mem_nhdsWithin_compl I_loc_mem_nhds_t {t}]
            with y hy_mem_Iloc_setminus_t
          rw [slope_def_module, h_phi_t_is_zero, sub_zero]
          by_cases hy_in_Imax : y ∈ I_max
          · simp [φ, hy_in_Imax, h_agree_on_inter ⟨hy_mem_Iloc_setminus_t.1, hy_in_Imax⟩]
          · simp [φ, hy_in_Imax]
        exact (tendsto_congr' h_slope_eventually_zero).mpr tendsto_const_nhds
      have deriv_sum := h_floc_deriv.add h_phi_deriv_zero
      rw [add_zero] at deriv_sum
      rw [show f_union t = f_loc t by simp [ht_in_I_max, f_union]]
      have : f_union = fun y => f_loc y + φ y := by
        funext y; by_cases hy : y ∈ I_max <;> simp [f_union, φ, hy]
      have h_deriv : HasDerivAt f_union (v t (f_loc t)) t := by
        simpa [this] using deriv_sum
      simpa using h_deriv.hasDerivWithinAt
  -- Maximality forces `I_max = I_loc ∪ I_max`, hence `I_loc ⊆ I_max`.
  rw [h_max.is_maximal (g := f_union) (J := I_loc ∪ I_max) h_union_sol
    (h_loc_open.union h_max.isOpen_domain) h_union_conn subset_union_right
    (fun t' ht' ↦ by simp [f_union, ht'])]
  exact subset_union_left

/--
If `(f₁, I₁)` and `(f₂, I₂)` are two maximal solutions to the same ODE `y' = v(t,y)`
passing through `(t₀, x₀)`, and `v(t,·)` is Lipschitz continuous with a uniform constant `K`
on the union of their domains `I₁ ∪ I₂`, then the maximal solutions are identical:
their domains are equal (`I₁ = I₂`), and the functions agree on this common domain.
-/
theorem IsMaximalODESolution.unique
  {f₁ f₂ : ℝ → E} {I₁ I₂ : Set ℝ}
  (h₁_max : IsMaximalODESolution v f₁ I₁)
  (h₂_max : IsMaximalODESolution v f₂ I₂)
  (ht₀₁ : t₀ ∈ I₁) (ht₀₂ : t₀ ∈ I₂)
  (hf₁_t₀ : f₁ t₀ = x₀) (hf₂_t₀ : f₂ t₀ = x₀)
  {K : ℝ≥0}
  (h_v_lipschitz_on_union : ∀ t ∈ I₁ ∪ I₂, LipschitzWith K (v t)) :
  I₁ = I₂ ∧ EqOn f₁ f₂ I₁ := by
  have h_v_lipschitz_on_inter : ∀ t ∈ I₁ ∩ I₂, LipschitzWith K (v t) := by
    intro t ht_in_inter
    exact h_v_lipschitz_on_union t (mem_union_left I₂ ht_in_inter.1)
  have h_I₁_subset_I₂ : I₁ ⊆ I₂ :=
    IsIntegralCurveOn.subset_maximal_domain_with_lipschitz v t₀ x₀
      h₁_max.isIntegralCurveOn h₁_max.isOpen_domain h₁_max.isConnected_domain ht₀₁ hf₁_t₀
      h₂_max ht₀₂ hf₂_t₀ h_v_lipschitz_on_inter
  have h_v_lipschitz_on_inter_symm : ∀ t ∈ I₂ ∩ I₁, LipschitzWith K (v t) := by
    simpa only [inter_comm, mem_inter_iff, and_imp] using h_v_lipschitz_on_inter
  have h_I₂_subset_I₁ : I₂ ⊆ I₁ :=
    IsIntegralCurveOn.subset_maximal_domain_with_lipschitz v t₀ x₀
      h₂_max.isIntegralCurveOn h₂_max.isOpen_domain h₂_max.isConnected_domain ht₀₂ hf₂_t₀
      h₁_max ht₀₁ hf₁_t₀ h_v_lipschitz_on_inter_symm
  have h_I_eq : I₁ = I₂ := h_I₁_subset_I₂.antisymm h_I₂_subset_I₁
  have h_v_lipschitz_on_I₁ : ∀ t ∈ I₁, LipschitzWith K (v t) := by
    intro t ht_in_I₁
    exact h_v_lipschitz_on_union t (mem_union_left I₂ ht_in_I₁)
  have h_eq_on_I₁ : EqOn f₁ f₂ (I₁ ∩ I₁) :=
    IsIntegralCurveOn.eqOn_of_agree_at_t₀_of_lipschitz (v := v) (t₀ := t₀)
      h₁_max.isIntegralCurveOn
      (by simpa only [h_I_eq] using h₂_max.isIntegralCurveOn)
      h₁_max.isOpen_domain
      (by simpa only [h_I_eq] using h₂_max.isOpen_domain)
      h₁_max.isConnected_domain
      (by simpa only [h_I_eq] using h₂_max.isConnected_domain)
      ht₀₁
      (by simpa only [h_I_eq] using ht₀₂)
      (by simp [hf₁_t₀, hf₂_t₀])
      (by
        intro t ht_in_I₁_inter_I₁
        exact h_v_lipschitz_on_I₁ t ht_in_I₁_inter_I₁.1)
  rw [inter_self] at h_eq_on_I₁
  exact ⟨h_I_eq, h_eq_on_I₁⟩

/-! ### Proof of Existence of Maximal Solutions -/

namespace MaximalSolutionExistence

section

/--
A local solution to the ODE, consisting of the function, its domain (an open interval),
and a proof that it satisfies the `IsIntegralCurveOn` predicate.

This structure is auxiliary for the Zorn's Lemma argument and is not intended for public use.
-/
private structure LocalODESolution (v : ℝ → E → E) (t₀ : ℝ) (x₀ : E) where
  /-- The function `f` which locally solves the ODE. -/
  f : ℝ → E
  /-- The open interval `I` on which `f` solves the ODE. -/
  I : Set ℝ
  isOpen : IsOpen I
  isConnected : IsConnected I
  t₀_mem : t₀ ∈ I
  f_t₀ : f t₀ = x₀
  deriv : IsIntegralCurveOn f v I

/--
The extension relation `p₁ ≤ p₂` for local ODE solutions `p₁` and `p₂`.
It means `p₂` is an extension of `p₁`, i.e., the domain of `p₁` is a subset of the domain
of `p₂`, and the functions agree on the smaller domain `p₁.I`.
-/
private def ODESolutionExtends (p₁ p₂ : LocalODESolution v t₀ x₀) : Prop :=
  p₁.I ⊆ p₂.I ∧ (EqOn p₁.f p₂.f p₁.I)

-- Define LE instance using the extension relation
private instance : LE (LocalODESolution v t₀ x₀) where
  le := ODESolutionExtends v t₀ x₀

-- Now define the Preorder instance. This is sufficient for `zorn_le_nonempty`.
private instance : Preorder (LocalODESolution v t₀ x₀) where
  le := ODESolutionExtends v t₀ x₀
  le_refl p := ⟨Subset.rfl, fun _ _ ↦ rfl⟩
  le_trans := fun _ _ _ h₁₂ h₂₃ =>
    ⟨h₁₂.1.trans h₂₃.1, fun _ ht ↦ (h₁₂.2 ht).trans (h₂₃.2 (h₁₂.1 ht))⟩

/--
The equivalence relation `≈` on local ODE solutions.
Two solutions are equivalent if they are extensions of each other, meaning
they have the same interval and agree on that interval.
This setoid structure is defined for completeness but not directly used by `zorn_le_nonempty`.
-/
private instance LocalODESolutionSetoid : Setoid (LocalODESolution v t₀ x₀) where
  r p₁ p₂ := p₁ ≤ p₂ ∧ p₂ ≤ p₁
  iseqv := {
    refl p := ⟨le_refl p, le_refl p⟩
    symm := And.symm
    trans h₁₂ h₂₃ := ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₂₃.2 h₁₂.2⟩
  }

/--
The quotient type of local ODE solutions, where solutions that are extensions
of each other are identified. This type carries the structure of a partial order.
This is defined for completeness but not directly used by `zorn_le_nonempty`.
-/
private abbrev QuotientLocalODESolution :=
  Quotient (LocalODESolutionSetoid (v:=v) (t₀:=t₀) (x₀:=x₀))

private instance QuotientLocalODESolution.instLE : LE (QuotientLocalODESolution v t₀ x₀) where
  le := Quotient.lift₂
    (fun p₁ p₂ => p₁ ≤ p₂)
    (by
      intro a₁ a₂ b₁ b₂ hab hcd
      apply propext
      apply Iff.intro
      · intro h_a1_le_a2
        calc
          b₁ ≤ a₁ := hab.2
          _  ≤ a₂ := h_a1_le_a2
          _  ≤ b₂ := hcd.1
      · intro h_b1_le_b2
        calc
          a₁ ≤ b₁ := hab.1
          _  ≤ b₂ := h_b1_le_b2
          _  ≤ a₂ := hcd.2
    )

/--
The set of local ODE solutions modulo the extension equivalence relation forms a partial order.
The order `⟦p₁⟧ ≤ ⟦p₂⟧` is induced by the preorder relation `p₁ ≤ p₂` on the representatives.
This instance is defined for completeness; `zorn_le_nonempty` operates on the `Preorder`
of `LocalODESolution` directly.
-/
private instance : PartialOrder (QuotientLocalODESolution v t₀ x₀) where
  le := (QuotientLocalODESolution.instLE v t₀ x₀).le
  le_refl := by
    rintro ⟨p⟩
    exact le_refl p
  le_trans := by
    rintro ⟨p₁⟩ ⟨p₂⟩ ⟨p₃⟩ h₁₂ h₂₃
    exact le_trans (α := LocalODESolution v t₀ x₀) h₁₂ h₂₃
  le_antisymm := by
    rintro ⟨p₁⟩ ⟨p₂⟩ h₁₂ h₂₁
    exact Quotient.sound ⟨h₁₂, h₂₁⟩


/--
If `C` is a chain of `LocalODESolution`s and `t` is in the domains of two solutions in `C`,
then those solutions agree at `t`. This is because chains are totally ordered by extension.
-/
private lemma chain_solutions_agree {C : Set (LocalODESolution v t₀ x₀)}
  (hC : IsChain (· ≤ ·) C) {p₁ p₂ : LocalODESolution v t₀ x₀}
    (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C)
    (t : ℝ) (ht₁ : t ∈ p₁.I) (ht₂ : t ∈ p₂.I) : p₁.f t = p₂.f t :=
  (hC.total hp₁ hp₂).elim (·.2 ht₁) fun h ↦ (h.2 ht₂).symm

open Classical in
/--
Constructs the supremum of a non-empty chain `C` of `LocalODESolution`s.
This supremum is itself a `LocalODESolution` and serves as an upper bound for `C`.
-/
private def chainSup (C : Set (LocalODESolution v t₀ x₀))
  (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) :
  LocalODESolution v t₀ x₀ := by
  -- The domain of the supremum solution is the union of the domains of solutions in the chain.
  let I_sup := ⋃ (p : LocalODESolution v t₀ x₀) (hp : p ∈ C), p.I
  -- The function of the supremum solution is defined by "gluing" the functions from the chain.
  -- For any t ∈ I_sup, pick any solution p ∈ C such that t ∈ p.I, and define f_sup(t) = p.f(t).
  -- This is well-defined because C is a chain.
  let f_sup : ℝ → E := fun t =>
    if ht : t ∈ I_sup then (Classical.choose (Set.mem_iUnion₂.mp ht)).f t else x₀
  -- Prove I_sup is an open interval containing t₀
  have I_sup_isOpen : IsOpen I_sup :=
    isOpen_iUnion fun p => isOpen_iUnion fun _ => p.isOpen
  have I_sup_isConnected : IsConnected I_sup := by
    have hne : I_sup.Nonempty := by
      obtain ⟨p, hp⟩ := hCne
      exact ⟨t₀, Set.mem_biUnion hp p.t₀_mem⟩
    let c : Set (Set ℝ) := LocalODESolution.I '' C
    have h_common_pt : ∀ s ∈ c, t₀ ∈ s := by
      rintro s ⟨p, hp, rfl⟩; exact p.t₀_mem
    have h_preconn : ∀ s ∈ c, IsPreconnected s := by
      rintro s ⟨p, hp, rfl⟩; exact p.isConnected.isPreconnected
    have h_preconn_union : IsPreconnected I_sup := by
      have I_sup_eq_sUnion_c : I_sup = ⋃₀ c := by
        ext x; simp only [mem_iUnion, exists_prop, mem_sUnion, I_sup]
        constructor
        · rintro ⟨p, hp, hx⟩
          refine ⟨p.I, ?_, hx⟩
          exact ⟨p, hp, rfl⟩
        · rintro ⟨s, ⟨p', hp', rfl⟩, hx_in_s⟩; use p'
      rw [I_sup_eq_sUnion_c]
      exact isPreconnected_sUnion t₀ c h_common_pt h_preconn
    exact ⟨hne, h_preconn_union⟩
  have I_sup_t₀_mem : t₀ ∈ I_sup := by
    obtain ⟨p, hp⟩ := hCne
    exact Set.mem_iUnion₂.mpr ⟨p, hp, p.t₀_mem⟩
  -- Prove f_sup satisfies the initial condition
  have f_sup_t₀ : f_sup t₀ = x₀ := by
    simp only [f_sup, dif_pos I_sup_t₀_mem]
    exact (Classical.choose (Set.mem_iUnion₂.mp I_sup_t₀_mem)).f_t₀
  -- Prove f_sup satisfies the derivative condition on I_sup
  have f_sup_deriv : IsIntegralCurveOn f_sup v I_sup := by
    intro t ht
    obtain ⟨p, hp, htp⟩ := Set.mem_iUnion₂.mp ht
    have f_sup_eq_pf_eventually : f_sup =ᶠ[𝓝 t] p.f := by
      filter_upwards [p.isOpen.mem_nhds htp] with y hy_in_pI
      have hy_in_I_sup : y ∈ I_sup := Set.mem_iUnion₂.mpr ⟨p, hp, hy_in_pI⟩
      simp only [f_sup, dif_pos hy_in_I_sup]
      have spec := Classical.choose_spec (Set.mem_iUnion₂.mp hy_in_I_sup)
      exact chain_solutions_agree (v := v) (t₀ := t₀) (x₀ := x₀) (C := C)
        hC spec.1 hp y spec.2 hy_in_pI
    have f_sup_eq_pft : f_sup t = p.f t := by
      simp only [f_sup, dif_pos ht]
      have spec := Classical.choose_spec (Set.mem_iUnion₂.mp ht)
      exact chain_solutions_agree (v := v) (t₀ := t₀) (x₀ := x₀) (C := C)
        hC spec.1 hp t spec.2 htp
    rw [f_sup_eq_pft]
    exact (((p.deriv t htp).hasDerivAt (p.isOpen.mem_nhds htp)).congr_of_eventuallyEq
      f_sup_eq_pf_eventually).hasDerivWithinAt
  exact { f := f_sup, I := I_sup, isOpen := I_sup_isOpen, isConnected := I_sup_isConnected,
          t₀_mem := I_sup_t₀_mem, f_t₀ := f_sup_t₀, deriv := f_sup_deriv }

open Classical in
/--
The `chainSup` construction provides an upper bound for any element `hp` in a non-empty chain `C`.
-/
private lemma chainSup_is_upper_bound (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) :
    ∀ hp ∈ C, hp ≤ chainSup v t₀ x₀ C hC hCne := by
  intro hp hpC
  refine ⟨fun t ht => Set.mem_iUnion₂.mpr ⟨hp, hpC, ht⟩, fun t ht => ?_⟩
  have ht_in_I_sup : t ∈ (chainSup v t₀ x₀ C hC hCne).I :=
    Set.mem_iUnion₂.mpr ⟨hp, hpC, ht⟩
  have ht_in_I_sup' : t ∈ ⋃ (p : LocalODESolution v t₀ x₀) (hp : p ∈ C), p.I := by
    simpa [chainSup] using ht_in_I_sup
  have ht_exists : ∃ i ∈ C, t ∈ i.I := by
    simpa [Set.mem_iUnion₂] using ht_in_I_sup'
  have h_eval : (chainSup v t₀ x₀ C hC hCne).f t =
      (Classical.choose (Set.mem_iUnion₂.mp ht_in_I_sup')).f t := by
    simp [chainSup, ht_exists]
  rw [h_eval]
  have spec := Classical.choose_spec (Set.mem_iUnion₂.mp ht_in_I_sup')
  exact chain_solutions_agree (v := v) (t₀ := t₀) (x₀ := x₀) (C := C)
    hC hpC spec.1 t ht spec.2

/--
Helper lemma stating that any non-empty chain `C` has an upper bound.
This is equivalent to `BddAbove C`.
-/
private lemma chain_has_upper_bound_explicit (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : ∃ ub, ∀ p ∈ C, p ≤ ub := by
  use chainSup v t₀ x₀ C hC hCne
  exact chainSup_is_upper_bound v t₀ x₀ C hC hCne

/--
Chains of local ODE solutions are bounded above. This is the condition required by
`zorn_le_nonempty`.
-/
private lemma chain_is_bddAbove (C : Set (LocalODESolution v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : BddAbove C := by
  -- `BddAbove C` means `∃ x, ∀ y ∈ C, y ≤ x`.
  -- This is exactly what `chain_has_upper_bound_explicit` provides.
  exact chain_has_upper_bound_explicit v t₀ x₀ C hC hCne

/--
The main existence theorem for maximal solutions within this namespace.
It asserts that if Picard-Lindelöf conditions guarantee a local solution on an
open interval `(tMin, tMax)` containing `t₀`, then a maximal solution exists.
-/
theorem exists_maximal_solution
  [CompleteSpace E]
  (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
  (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
  (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
  ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalODESolution v f I ∧ t₀ ∈ I ∧ f t₀ = x₀ := by
  let S := LocalODESolution v t₀ x₀
  -- 1. Show S is non-empty using the guaranteed local solution from Picard-Lindelöf.
  have S_nonempty_instance : Nonempty S := by
    -- Picard-Lindelöf gives a solution `f₀` on `Icc tMin tMax`.
    have hx₀ : x₀ ∈ Metric.closedBall x₀ r := by simp
    rcases (IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hpl_instance hx₀)
      with ⟨f₀, hf₀_t₀, hf₀_deriv_within⟩
    -- Convert `HasDerivWithinAt` on `Icc` to `HasDerivAt` on `Ioo`.
    have hf₀_deriv_at : ∀ t ∈ Ioo tMin tMax, HasDerivAt f₀ (v t (f₀ t)) t := by
      intro t ht_local_prop
      specialize hf₀_deriv_within t (Ioo_subset_Icc_self ht_local_prop)
      -- Since `t_mem_I_local` is in the interior `I_local` of `Icc tMin tMax`,
      -- `HasDerivWithinAt` implies `HasDerivAt`.
      apply hf₀_deriv_within.hasDerivAt (Icc_mem_nhds ht_local_prop.1 ht_local_prop.2)
    -- Construct the initial `LocalODESolution`.
    let p₀ : LocalODESolution v t₀ x₀ := {
      f := f₀, I := Ioo tMin tMax,
      isOpen := isOpen_Ioo,
      isConnected := isConnected_Ioo (htMin_lt_t₀.trans ht₀_lt_tMax),
      t₀_mem := ⟨htMin_lt_t₀, ht₀_lt_tMax⟩,
      f_t₀ := by simpa [ht₀'_eq] using hf₀_t₀,
      deriv := by intro t ht; exact (hf₀_deriv_at t ht).hasDerivWithinAt
    }
    exact ⟨p₀⟩
  -- 2. Apply Zorn's Lemma for Preorders (`zorn_le_nonempty`).
  -- This requires that every non-empty chain has an upper bound (`BddAbove`).
  rcases zorn_le_nonempty (chain_is_bddAbove v t₀ x₀) with
    ⟨maximal_element, h_is_max_elem⟩
    -- `h_is_max_elem` means `∀ (x : S), maximal_element ≤ x → x ≤ maximal_element`.
  -- 3. Show this `maximal_element` corresponds to an `IsMaximalODESolution`.
  use maximal_element.f, maximal_element.I
  refine ⟨?_, maximal_element.t₀_mem, maximal_element.f_t₀⟩
  refine ⟨maximal_element.isOpen, maximal_element.isConnected, maximal_element.deriv, ?_⟩
  -- Prove the maximality condition.
  intro g J hg_sol hJ_open hJ_conn hIJ_subset h_eq_on_I
  -- Assume, for contradiction, that `I ≠ J`.
  by_contra h_I_ne_J
  -- Construct a `LocalODESolution` from `(g, J)`.
  let p_g : LocalODESolution v t₀ x₀ :=
    { f := g, I := J,
      isOpen := hJ_open,
      isConnected := hJ_conn,
      t₀_mem := hIJ_subset maximal_element.t₀_mem,
      f_t₀ := by
        have h_eq_at_t₀ : g t₀ = maximal_element.f t₀ := by
          symm
          exact h_eq_on_I maximal_element.t₀_mem
        simpa [h_eq_at_t₀] using maximal_element.f_t₀,
      deriv := hg_sol }
  exact h_I_ne_J (hIJ_subset.antisymm (h_is_max_elem (b := p_g) ⟨hIJ_subset, h_eq_on_I⟩).1)

end

end MaximalSolutionExistence

/--
Under the conditions of the Picard-Lindelöf theorem (specifically, ensuring local existence
on an open interval around `t₀`), there exists a maximal solution to the ODE `x' = v(t, x)`
with initial condition `f(t₀) = x₀`.
-/
theorem exists_maximal_ode_solution [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalODESolution v f I ∧ t₀ ∈ I ∧ f t₀ = x₀ := by
  obtain ⟨f, I, hmax⟩ :=
    MaximalSolutionExistence.exists_maximal_solution v t₀ x₀
      tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance
  exact ⟨f, I, hmax⟩

open Classical in
/--
An arbitrarily chosen maximal solution to the ODE `x' = v(t, x)` through `(t₀, x₀)`, obtained
by choice from `exists_maximal_ode_solution` under the Picard–Lindelöf hypotheses.

This is a total function `ℝ → E`; it is only guaranteed to satisfy the ODE on the corresponding
domain `maximalODESolutionDomain`.
-/
noncomputable def maximalODESolution [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) : ℝ → E :=
  Classical.choose (exists_maximal_ode_solution v t₀ x₀ tMin tMax a r L K t₀'
    ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance)

open Classical in
/--
The maximal open connected domain of the chosen maximal solution `maximalODESolution`.

This set is obtained by choice from `exists_maximal_ode_solution` under the Picard–Lindelöf
hypotheses; it contains `t₀` and on it the function `maximalODESolution` is an integral curve
of `v` with initial value `x₀`.
-/
noncomputable def maximalODESolutionDomain [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) : Set ℝ :=
  Classical.choose (Classical.choose_spec
    (exists_maximal_ode_solution v t₀ x₀ tMin tMax a r L K t₀'
      ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance))

open Classical in
private lemma maximalODESolution_spec_of_exists [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    IsMaximalODESolution v
      (maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      (maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      ∧ t₀ ∈ maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
        ht₀_lt_tMax hpl_instance
      ∧ maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance t₀ = x₀ := by
  simpa [maximalODESolution, maximalODESolutionDomain] using
    (Classical.choose_spec
      (Classical.choose_spec
        (exists_maximal_ode_solution v t₀ x₀ tMin tMax a r L K t₀'
          ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance)))

open Classical in
lemma maximalODESolution_spec [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    IsMaximalODESolution v
      (maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      (maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      ∧ t₀ ∈ maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
        ht₀_lt_tMax hpl_instance
      ∧ maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance t₀ = x₀ := by
  simpa using maximalODESolution_spec_of_exists v t₀ x₀ tMin tMax a r L K t₀'
    ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance

lemma maximalODESolution_isMaximal [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    IsMaximalODESolution v
      (maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      (maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance) :=
  (maximalODESolution_spec v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).1

lemma maximalODESolution_t₀_mem [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    t₀ ∈ maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
      ht₀_lt_tMax hpl_instance :=
  (maximalODESolution_spec v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).2.1

lemma maximalODESolution_t₀_eq [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance t₀ = x₀ :=
  (maximalODESolution_spec v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).2.2

lemma maximalODESolution_isSolution [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    IsIntegralCurveOn
      (maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      v
      (maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance) :=
  (maximalODESolution_isMaximal v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).isIntegralCurveOn

theorem maximalODESolution_unique [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K)
    {f₂ : ℝ → E} {I₂ : Set ℝ}
    (h₂_max : IsMaximalODESolution v f₂ I₂)
    (ht₀₂ : t₀ ∈ I₂) (hf₂_t₀ : f₂ t₀ = x₀)
    {K' : ℝ≥0}
    (h_v_lipschitz_on_union :
        ∀ t ∈
          maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
            ht₀_lt_tMax hpl_instance ∪ I₂,
          LipschitzWith K' (v t)) :
    maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance = I₂
      ∧ EqOn
        (maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
          hpl_instance)
        f₂
        (maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
          ht₀_lt_tMax hpl_instance) := by
  have h₁_max : IsMaximalODESolution v
      (maximalODESolution v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      (maximalODESolutionDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance) :=
    maximalODESolution_isMaximal v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance
  exact IsMaximalODESolution.unique v t₀ x₀
    h₁_max h₂_max
    (maximalODESolution_t₀_mem v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance)
    ht₀₂
    (maximalODESolution_t₀_eq v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance)
    hf₂_t₀ h_v_lipschitz_on_union
