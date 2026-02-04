/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

public section

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Set α} {a ε : α}

theorem IsGLB.exists_between_self_add (h : IsGLB s a) (hε : 0 < ε) : ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
  h.exists_between <| lt_add_of_pos_right _ hε

theorem IsGLB.exists_between_self_add' (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a < b ∧ b < a + ε :=
  h.exists_between' h₂ <| lt_add_of_pos_right _ hε

theorem IsLUB.exists_between_sub_self (h : IsLUB s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
  h.exists_between <| sub_lt_self _ hε

theorem IsLUB.exists_between_sub_self' (h : IsLUB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a - ε < b ∧ b < a :=
  h.exists_between' h₂ <| sub_lt_self _ hε

end LinearOrderedAddCommGroup

section OrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {s : Set α}

theorem BddAbove_preimage_neg (h : BddBelow s) : BddAbove (Neg.neg ⁻¹' s) := by
  rcases h with ⟨b, hb⟩
  use -b
  intro x hx
  have hx' : -x ∈ s := hx
  have hle : b ≤ -x := hb hx'
  have hle' : x ≤ -b := (neg_le_neg_iff).1 (by simpa using hle)
  simpa using hle'

end OrderedAddCommGroup

section ConditionallyCompleteLinearOrder

variable {α : Type*} [ConditionallyCompleteLinearOrder α]
  [AddCommGroup α] [IsOrderedAddMonoid α] {s : Set α}

theorem sSup_preimage_neg (h : s.Nonempty) (h_bdd : BddBelow s) :
    sSup (Neg.neg ⁻¹' s) = -sInf s := by
  classical
  have hpre_nonempty : (Neg.neg ⁻¹' s).Nonempty := by
    rcases h with ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    simpa using hy
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hpre_nonempty ?_ ?_
  · intro a ha
    have ha' : -a ∈ s := ha
    have hle : sInf s ≤ -a := csInf_le h_bdd ha'
    have hle' : -(-a) ≤ -sInf s := (neg_le_neg_iff).2 hle
    simpa [neg_neg] using hle'
  · intro w hw
    have h' : sInf s < -w := by
      have hw' : -(-w) < -sInf s := by simpa using hw
      exact (neg_lt_neg_iff).1 hw'
    rcases (csInf_lt_iff h_bdd h).1 h' with ⟨y, hy, hy_lt⟩
    refine ⟨-y, ?_, ?_⟩
    · simpa using hy
    · have : -(-w) < -y := (neg_lt_neg_iff).2 hy_lt
      simpa using this

end ConditionallyCompleteLinearOrder
