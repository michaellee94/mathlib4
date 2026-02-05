/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.Geometry.Manifold.JetBundle.Defs
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# Jet coordinate-change maps

This file introduces algebraic coordinate-change operations on jets, expressed
via Taylor composition of formal multilinear series. These are the building
blocks for defining jet bundle transition maps.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Jet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {r : ℕ}

/--
Coordinate-change on jets, defined by Taylor composition:
postcompose by `β` and precompose by `α` (both at the given basepoints),
then truncate to order `r`.

This is the algebraic operation used in jet bundle chart transitions.
-/
noncomputable def coordChange (r : ℕ) (x : E) (y : F) (α : E → E) (β : F → G)
    (j : Jet 𝕜 E F r) : Jet 𝕜 E G r :=
  let hnr : r ≤ (r : ℕ∞) := le_rfl
  let jα : Jet 𝕜 E E r := jetOf (r := r) (n := (r : ℕ∞)) hnr α x
  let jβ : Jet 𝕜 F G r := jetOf (r := r) (n := (r : ℕ∞)) hnr β y
  Jet.taylorComp jβ (Jet.taylorComp j jα)

lemma taylorComp_eq_of_eq_on
    {p p' : Jet 𝕜 E F r} {q q' : Jet 𝕜 F G r}
    (hp : ∀ m ≤ r, Jet.toFMS p m = Jet.toFMS p' m)
    (hq : ∀ m ≤ r, Jet.toFMS q m = Jet.toFMS q' m) :
    Jet.taylorComp q p = Jet.taylorComp q' p' := by
  apply Jet.ext
  intro k
  have hk : (k : ℕ) ≤ r := Nat.le_of_lt_succ k.is_lt
  have hcomp := FormalMultilinearSeries.taylorComp_eq_of_eq_on
    (p := Jet.toFMS p) (p' := Jet.toFMS p') (q := Jet.toFMS q) (q' := Jet.toFMS q') (n := k)
    (fun m hm => hp m (le_trans hm hk))
    (fun m hm => hq m (le_trans hm hk))
  simpa [Jet.taylorComp, Jet.truncate] using hcomp

lemma jetOf_comp (f : E → F) (g : F → G) (x : E)
    (hf : ContDiff 𝕜 (r : WithTop ℕ∞) f) (hg : ContDiff 𝕜 (r : WithTop ℕ∞) g) :
    jetOf (𝕜 := 𝕜) (E := E) (F := G) (r := r) (n := (r : ℕ∞)) le_rfl (g ∘ f) x =
      Jet.taylorComp
        (jetOf (𝕜 := 𝕜) (E := F) (F := G) (r := r) (n := (r : ℕ∞)) le_rfl g (f x))
        (jetOf (𝕜 := 𝕜) (E := E) (F := F) (r := r) (n := (r : ℕ∞)) le_rfl f x) := by
  apply Jet.ext
  intro k
  set kNat : ℕ := (k : ℕ)
  have hk : kNat ≤ r := Nat.le_of_lt_succ k.is_lt
  have hk' : (kNat : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) := by
    exact_mod_cast hk
  have hp : ∀ m ≤ kNat, Jet.toFMS (jetOf (𝕜 := 𝕜) (E := E) (F := F)
      (r := r) (n := (r : ℕ∞)) le_rfl f x) m =
      ftaylorSeries 𝕜 f x m := by
    intro m hm
    exact Jet.toFMS_jetOf_eq (hn := le_rfl) (f := f) (x := x) (k := m) (hk := le_trans hm hk)
  have hq : ∀ m ≤ kNat, Jet.toFMS (jetOf (𝕜 := 𝕜) (E := F) (F := G)
      (r := r) (n := (r : ℕ∞)) le_rfl g (f x)) m =
      ftaylorSeries 𝕜 g (f x) m := by
    intro m hm
    exact Jet.toFMS_jetOf_eq (hn := le_rfl) (f := g) (x := f x) (k := m) (hk := le_trans hm hk)
  have hcomp := FormalMultilinearSeries.taylorComp_eq_of_eq_on (n := kNat) hp hq
  have hg' : ContDiffAt 𝕜 (r : WithTop ℕ∞) g (f x) := hg.contDiffAt
  have hf' : ContDiffAt 𝕜 (r : WithTop ℕ∞) f x := hf.contDiffAt
  have hderiv :=
    iteratedFDeriv_comp (n := (r : WithTop ℕ∞)) (x := x) (f := f) (g := g) hg' hf' hk'
  have hft : ftaylorSeries 𝕜 (g ∘ f) x kNat =
      (ftaylorSeries 𝕜 g (f x)).taylorComp (ftaylorSeries 𝕜 f x) kNat := by
    simpa [ftaylorSeries] using hderiv
  calc
    (jetOf (𝕜 := 𝕜) (E := E) (F := G) (r := r) (n := (r : ℕ∞)) le_rfl (g ∘ f) x).coeff k
        = ftaylorSeries 𝕜 (g ∘ f) x kNat := by simp [jetOf, kNat]
    _ = (ftaylorSeries 𝕜 g (f x)).taylorComp (ftaylorSeries 𝕜 f x) kNat := hft
    _ = (Jet.taylorComp
          (jetOf (𝕜 := 𝕜) (E := F) (F := G) (r := r) (n := (r : ℕ∞)) le_rfl g (f x))
          (jetOf (𝕜 := 𝕜) (E := E) (F := F) (r := r) (n := (r : ℕ∞)) le_rfl f x)).coeff k := by
      simpa [Jet.taylorComp, Jet.truncate, jetOf, kNat] using hcomp.symm

end Jet
