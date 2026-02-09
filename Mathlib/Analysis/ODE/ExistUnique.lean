/-
Copyright (c) 2026 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Transform

/-!
# Existence and uniqueness of integral curves in normed spaces

This file states the results of Gronwall's inequality and the Picard-Lindelöf theorem in terms
of the integral curve API (`IsIntegralCurve`, `IsIntegralCurveOn`, `IsIntegralCurveAt`).

## Main results

* `ContDiffAt.exists_isIntegralCurveAt`: local existence of integral curves for a time-independent
  $C^1$ vector field, via the Picard-Lindelöf theorem.
* `isIntegralCurveAt_eventuallyEq`: local uniqueness of integral curves for a Lipschitz vector
  field, via Gronwall's inequality.
* `isIntegralCurveOn_Ioo_eqOn`: uniqueness of integral curves on an open interval.
* `isIntegralCurve_eq`: global uniqueness of integral curves.

## Tags

integral curve, vector field, existence, uniqueness, Picard-Lindelöf, Gronwall
-/
