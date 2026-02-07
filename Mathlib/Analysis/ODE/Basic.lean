/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Integral curves of vector fields on a normed vector space

Let `E` be a normed vector space and `v : ℝ → E → E` be a time-dependent vector field on `E`.
An integral curve  of `v` is a function `γ : ℝ → E` such that the derivative of `γ` at `t` equals
`v t (γ t)`. The integral curve may only be defined for all `t` within some subset of `ℝ`.

## Main definitions

Let `v : ℝ → E → E` be a time-dependent vector field on `E`, and let `γ : ℝ → E`.
* `IsIntegralCurve γ v`: `γ t` is tangent to `v t (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsIntegralCurveOn γ v s`: `γ t` is tangent to `v t (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsIntegralCurveAt γ v t₀`: `γ t` is tangent to `v t (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

## TODO

* Implement `IsIntegralCurveWithinAt`.

## Tags

integral curve, vector field
-/

@[expose] public section

open scoped Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `IsIntegralCurveOn γ v s` means `γ t` is tangent to `v t (γ t)` within `s` for all `t ∈ s`. -/
def IsIntegralCurveOn (γ : ℝ → E) (v : ℝ → E → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt γ (v t (γ t)) s t

/-- Extend a vector field defined on an open domain `U ⊆ ℝ × E` to all of `ℝ × E`
by setting it to `0` outside `U`. -/
noncomputable def extendVectorField (U : Set (ℝ × E))
    (v : {p : ℝ × E // p ∈ U} → E) : ℝ → E → E :=
  by
    classical
    intro t x
    exact if h : (t, x) ∈ U then v ⟨(t, x), h⟩ else 0

/-- A domain-restricted integral curve: the trajectory stays in `U` and solves the ODE
for the zero-extension of `v`. -/
def IsIntegralCurveOnWithin (γ : ℝ → E) (U : Set (ℝ × E))
    (v : {p : ℝ × E // p ∈ U} → E) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, (t, γ t) ∈ U) ∧ IsIntegralCurveOn γ (extendVectorField (E := E) U v) s

/-- `IsIntegralCurveAt γ v t₀` means `γ : ℝ → E` is a local integral curve of `v` in a neighbourhood
containing `t₀`. -/
def IsIntegralCurveAt (γ : ℝ → E) (v : ℝ → E → E) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (v t (γ t)) t

/-- `IsIntegralCurve γ v` means `γ : ℝ → E` is a global integral curve of `v`. That is, `γ t` is
tangent to `v t (γ t)` for all `t : ℝ`. -/
def IsIntegralCurve (γ : ℝ → E) (v : ℝ → E → E) : Prop :=
  ∀ t : ℝ, HasDerivAt γ (v t (γ t)) t

variable {γ γ' : ℝ → E} {v : ℝ → E → E} {s s' : Set ℝ} {t₀ : ℝ}

omit [NormedSpace ℝ E] in
lemma extendVectorField_apply_of_mem {U : Set (ℝ × E)}
    {v : {p : ℝ × E // p ∈ U} → E} {t : ℝ} {x : E} (h : (t, x) ∈ U) :
    extendVectorField U v t x = v ⟨(t, x), h⟩ := by
  classical
  simp [extendVectorField, h]

omit [NormedSpace ℝ E] in
lemma extendVectorField_apply_of_not_mem {U : Set (ℝ × E)}
    {v : {p : ℝ × E // p ∈ U} → E} {t : ℝ} {x : E} (h : (t, x) ∉ U) :
    extendVectorField U v t x = 0 := by
  classical
  simp [extendVectorField, h]

lemma IsIntegralCurveOnWithin.mapsTo {U : Set (ℝ × E)}
    {v : {p : ℝ × E // p ∈ U} → E} {γ : ℝ → E} {s : Set ℝ}
    (h : IsIntegralCurveOnWithin γ U v s) :
    ∀ t ∈ s, (t, γ t) ∈ U := h.1

lemma IsIntegralCurveOnWithin.isIntegralCurveOn {U : Set (ℝ × E)}
    {v : {p : ℝ × E // p ∈ U} → E} {γ : ℝ → E} {s : Set ℝ}
    (h : IsIntegralCurveOnWithin γ U v s) :
    IsIntegralCurveOn γ (extendVectorField U v) s := h.2

lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set ℝ) :
    IsIntegralCurveOn γ v s := fun t _ ↦ (h t).hasDerivWithinAt

lemma isIntegralCurveOn_univ :
    IsIntegralCurveOn γ v univ ↔ IsIntegralCurve γ v :=
  ⟨fun h t ↦ (h t (mem_univ _)).hasDerivAt Filter.univ_mem, fun h ↦ h.isIntegralCurveOn _⟩

lemma isIntegralCurveAt_iff_exists_mem_nhds :
    IsIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsIntegralCurveOn γ v s := by
  rw [IsIntegralCurveAt, Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, fun t ht ↦ (h t ht).hasDerivWithinAt⟩, ?_⟩
  intro ⟨s, hs, h⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨s', h₁, h₂, h₃⟩ := hs
  refine ⟨s', h₂.mem_nhds h₃, ?_⟩
  intro t ht
  apply (h t (h₁ ht)).hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨s', h₁, h₂, ht⟩

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
lemma isIntegralCurveAt_iff_exists_pos :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [IsIntegralCurveAt, Metric.eventually_nhds_iff_ball]
  constructor
  · rintro ⟨ε, hε, hγ⟩
    exact ⟨ε, hε, fun t ht ↦ (hγ t ht).hasDerivWithinAt⟩
  · rintro ⟨ε, hε, hγ⟩
    exact ⟨ε, hε, fun t ht ↦ (hγ t ht).hasDerivAt (Metric.isOpen_ball.mem_nhds ht)⟩

lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t :=
  isIntegralCurveAt_iff_exists_mem_nhds.mpr
    ⟨univ, Filter.univ_mem, fun t _ ↦ (h t).hasDerivWithinAt⟩

lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp (h t)
    exact h t (mem_of_mem_nhds hs) |>.hasDerivAt hs⟩

lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht ↦ h t (hs ht) |>.mono hs

lemma IsIntegralCurveAt.hasDerivAt (h : IsIntegralCurveAt γ v t₀) :
    HasDerivAt γ (v t₀ (γ t₀)) t₀ :=
  have ⟨_, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp h
  h t₀ (mem_of_mem_nhds hs) |>.hasDerivAt hs

lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsIntegralCurveAt γ v t₀ := isIntegralCurveAt_iff_exists_mem_nhds.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`. -/
lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs') |>.hasDerivWithinAt

lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

lemma IsIntegralCurveOn.continuousWithinAt (hγ : IsIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).continuousWithinAt

lemma IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := (hγ · · |>.continuousWithinAt)

lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp hγ
  hγ.continuousWithinAt (mem_of_mem_nhds hs) |>.continuousAt hs

lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr (hγ.isIntegralCurveAt · |>.continuousAt)

/-! ### Autonomization: Converting time-dependent ODEs to autonomous form

A time-dependent ODE `x' = v(t, x)` can be converted to an autonomous system on the extended
phase space `E × ℝ` by treating time as a state variable:
```
(x, τ)' = (v(τ, x), 1)
```
This section provides lemmas for converting integral curves between these formulations.
-/

/-- Convert a time-dependent integral curve to an autonomous one on the extended space `E × ℝ`.
The extended curve is `t ↦ (γ t, t)` and the extended vector field is `(x, τ) ↦ (v τ x, 1)`. -/
lemma IsIntegralCurveOn.toExtended (h : IsIntegralCurveOn γ v s) :
    IsIntegralCurveOn (fun t => (γ t, t)) (fun _ p => (v p.2 p.1, (1 : ℝ))) s := by
  intro t ht
  exact (h t ht).prodMk (hasDerivWithinAt_id t s)

/-- Convert a time-dependent integral curve to an autonomous one (global version). -/
lemma IsIntegralCurve.toExtended (h : IsIntegralCurve γ v) :
    IsIntegralCurve (fun t => (γ t, t)) (fun _ p => (v p.2 p.1, (1 : ℝ))) := by
  intro t
  exact (h t).prodMk (hasDerivAt_id t)

/-- Properness of the extended curve `t ↦ (t, γ t)` on a domain `I`, expressed via compact
preimages. -/
def IsProperExtendedCurve (γ : ℝ → E) (I : Set ℝ) : Prop :=
  ∀ K : Set (ℝ × E), IsCompact K → IsCompact {t : I | ((t : ℝ), γ t) ∈ K}

/-- The first component of an extended integral curve is an integral curve of the original
time-dependent system, provided the second component derivative is 1 and equals `v`. -/
lemma IsIntegralCurveOn.ofExtended_fst {Γ : ℝ → E × ℝ}
    (h : IsIntegralCurveOn Γ (fun _ p => (v p.2 p.1, (1 : ℝ))) s)
    (hΓ_snd : ∀ t ∈ s, (Γ t).2 = t) :
    IsIntegralCurveOn (fun t => (Γ t).1) v s := by
  intro t ht
  have hΓ := h t ht
  have h_fst : HasDerivWithinAt (fun τ => (Γ τ).1) (v (Γ t).2 (Γ t).1) s t :=
    hΓ.fst
  simp only [hΓ_snd t ht] at h_fst
  exact h_fst
