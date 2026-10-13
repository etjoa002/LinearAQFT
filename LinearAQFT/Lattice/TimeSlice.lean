/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Lattice.Propagator
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Group.Int

/-!
# The time-slice construction on the lattice

For a test function `f`, a time `t₁` and `u = E f`, the function `f' = P((1 - χ) u)`, with
`χ = [t ≥ t₁ + 1]`, is supported on the two slices `S_{t₁}` inside the causal shadow of
`supp f`, and `E f' = E f`.

## Main statements

* `timeSlice_support`, `causalProp_timeSlice` (E1, Theorem 10).
* `exists_causalProp_eq_of_dependent` (E1, Corollary 11).
-/

noncomputable section

namespace LinearAQFT

namespace Lattice

variable (m2 : ℝ)

/-- The past part `(1 - χ) u`: `u` at times `≤ t₁`, zero afterwards. -/
def pastPart (t₁ : ℤ) (u : Point → ℝ) (p : Point) : ℝ := if p.1 ≤ t₁ then u p else 0

theorem comparable_of_abs_le {p q : Point} (h : |p.2 - q.2| ≤ |p.1 - q.1|) : Comparable p q := by
  unfold Comparable causalLE
  rcases le_total q.1 p.1 with hle | hle
  · right; rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ p.1 - q.1)] at h; exact h
  · left
    rw [abs_of_nonpos (by linarith : p.1 - q.1 ≤ 0)] at h
    rw [abs_sub_comm]; linarith

/-- The support of `E f` lies strictly inside the causal shadow of `supp f`. -/
theorem causalProp_support {f : TestFun} {r : Point} (h : causalProp m2 f r ≠ 0) :
    ∃ q ∈ f.support, |r.2 - q.2| ≤ |r.1 - q.1| - 1 := by
  simp only [causalProp, Pi.sub_apply] at h
  by_cases ha : advanced m2 f r = 0
  · rw [ha, zero_sub, neg_ne_zero] at h
    obtain ⟨q, hq, hrq⟩ := retarded_support m2 h
    exact ⟨q, hq, by have := le_abs_self (r.1 - q.1); linarith⟩
  · obtain ⟨q, hq, hrq⟩ := advanced_support m2 ha
    exact ⟨q, hq, by have := neg_abs_le (r.1 - q.1); linarith⟩

/-- The function `P((1 - χ) E f)`. -/
def timeSliceFun (f : TestFun) (t₁ : ℤ) : Point → ℝ :=
  kgOp m2 (pastPart t₁ (causalProp m2 f))

theorem timeSliceFun_eq (f : TestFun) (t₁ : ℤ) (p : Point) :
    timeSliceFun m2 f t₁ p =
      if p.1 = t₁ then -causalProp m2 f (t₁ + 1, p.2)
      else if p.1 = t₁ + 1 then causalProp m2 f (t₁, p.2) else 0 := by
  have hu := kgOp_causalProp m2 f p
  simp only [timeSliceFun, kgOp, pastPart] at hu ⊢
  obtain ⟨t, x⟩ := p
  simp only at hu ⊢
  split_ifs <;> (try subst_vars) <;>
    (try simp only [add_sub_cancel_right] at hu ⊢) <;> first | omega | linarith

theorem timeSliceFun_ne_zero {f : TestFun} {t₁ : ℤ} {p : Point}
    (h : timeSliceFun m2 f t₁ p ≠ 0) : p ∈ slices t₁ ∧ p ∈ causalShadow (↑f.support) := by
  rw [timeSliceFun_eq] at h
  split_ifs at h with h1 h2
  · refine ⟨Or.inl h1, ?_⟩
    obtain ⟨q, hq, hpq⟩ := causalProp_support m2 (neg_ne_zero.1 h)
    refine ⟨q, hq, comparable_of_abs_le ?_⟩
    simp only at hpq
    rw [h1]
    have := abs_sub_abs_le_abs_sub (t₁ + 1 - q.1) (t₁ - q.1)
    rw [show t₁ + 1 - q.1 - (t₁ - q.1) = 1 by ring] at this
    simp at this
    linarith
  · refine ⟨Or.inr h2, ?_⟩
    obtain ⟨q, hq, hpq⟩ := causalProp_support m2 h
    refine ⟨q, hq, comparable_of_abs_le ?_⟩
    simp only at hpq
    rw [h2]
    have := abs_sub_abs_le_abs_sub (t₁ - q.1) (t₁ + 1 - q.1)
    rw [show t₁ - q.1 - (t₁ + 1 - q.1) = -1 by ring] at this
    simp at this
    linarith
  · exact absurd rfl h

/-- A finite set containing the support of `P((1 - χ) E f)`. -/
def timeSliceFinset (f : TestFun) (t₁ : ℤ) : Finset Point :=
  f.support.biUnion fun q =>
    ({t₁, t₁ + 1} : Finset ℤ) ×ˢ Finset.Icc (q.2 - |t₁ - q.1| - 1) (q.2 + |t₁ - q.1| + 1)

theorem mem_timeSliceFinset {f : TestFun} {t₁ : ℤ} {p : Point} (h : timeSliceFun m2 f t₁ p ≠ 0) :
    p ∈ timeSliceFinset f t₁ := by
  obtain ⟨hs, q, hq, hpq⟩ := timeSliceFun_ne_zero m2 h
  simp only [timeSliceFinset, Finset.mem_biUnion, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_Icc]
  refine ⟨q, hq, hs, ?_⟩
  have hab : |p.2 - q.2| ≤ |p.1 - q.1| := by
    rcases hpq with h' | h'
    · unfold causalLE at h'; rw [abs_sub_comm] at h'
      exact h'.trans (by rw [abs_sub_comm]; exact le_abs_self _)
    · unfold causalLE at h'; exact h'.trans (le_abs_self _)
  have ht : |p.1 - q.1| ≤ |t₁ - q.1| + 1 := by
    rcases hs with e | e <;> rw [e]
    · exact le_add_of_nonneg_right zero_le_one
    · have := abs_add_le (t₁ - q.1) 1
      rw [show t₁ - q.1 + 1 = t₁ + 1 - q.1 by ring] at this
      simpa using this
  rw [abs_le] at hab
  constructor <;> linarith [abs_nonneg (p.1 - q.1)]

/-- E1, Theorem 10: the test function `f' = P((1 - χ) E f)`. -/
def timeSlice (f : TestFun) (t₁ : ℤ) : TestFun :=
  Finsupp.onFinset (timeSliceFinset f t₁) (timeSliceFun m2 f t₁)
    (fun _ h => mem_timeSliceFinset m2 h)

theorem timeSlice_apply (f : TestFun) (t₁ : ℤ) (p : Point) :
    timeSlice m2 f t₁ p = timeSliceFun m2 f t₁ p := rfl

/-- E1, Theorem 10: `supp f' ⊆ S_{t₁} ∩ J(supp f)`. -/
theorem timeSlice_support (f : TestFun) (t₁ : ℤ) :
    (↑(timeSlice m2 f t₁).support : Set Point) ⊆ slices t₁ ∩ causalShadow (↑f.support) :=
  fun _ hp => timeSliceFun_ne_zero m2 (Finsupp.mem_support_iff.1 hp)

theorem timeSlice_time {f : TestFun} {t₁ : ℤ} {q : Point}
    (hq : q ∈ (timeSlice m2 f t₁).support) : t₁ ≤ q.1 ∧ q.1 ≤ t₁ + 1 := by
  have := (timeSlice_support m2 f t₁ hq).1
  rcases this with e | e <;> simp only [e] <;> omega

/-- E1, Theorem 10: `E f' = E f`. -/
theorem causalProp_timeSlice (f : TestFun) (t₁ : ℤ) :
    causalProp m2 (timeSlice m2 f t₁) = causalProp m2 f := by
  set u := causalProp m2 f
  set f' := timeSlice m2 f t₁
  have hf' : ⇑f' = kgOp m2 (pastPart t₁ u) := funext fun p => rfl
  have hPu : kgOp m2 u = 0 := funext (kgOp_causalProp m2 f)
  -- G⁺ f' = (1 - χ) u - u
  have hret : retarded m2 f' = pastPart t₁ u - u := by
    have h := eq_zero_of_kgOp_eq_zero_of_past m2 (u := retarded m2 f' - (pastPart t₁ u - u))
      (fun p => by
        rw [kgOp_sub, kgOp_sub, hPu]
        simp only [Pi.sub_apply, kgOp_retarded, hf', sub_zero, sub_self])
      (t₁ + 1) (fun p hp => by
        simp only [Pi.sub_apply]
        have h1 : retarded m2 f' p = 0 := by
          by_contra hne
          obtain ⟨q, hq, hpq⟩ := retarded_support m2 hne
          have := (timeSlice_time m2 hq).1
          have := abs_nonneg (p.2 - q.2)
          omega
        have h2 : pastPart t₁ u p = u p := by
          simp only [pastPart]; split_ifs with h
          · rfl
          · omega
        rw [h1, h2, sub_self, sub_zero])
    exact sub_eq_zero.1 h
  -- G⁻ f' = (1 - χ) u
  have hadv : advanced m2 f' = pastPart t₁ u := by
    have h := eq_zero_of_kgOp_eq_zero_of_future m2 (u := advanced m2 f' - pastPart t₁ u)
      (fun p => by
        rw [kgOp_sub]
        simp only [Pi.sub_apply, kgOp_advanced, hf', sub_self])
      t₁ (fun p hp => by
        simp only [Pi.sub_apply]
        have h1 : advanced m2 f' p = 0 := by
          by_contra hne
          obtain ⟨q, hq, hpq⟩ := advanced_support m2 hne
          have := (timeSlice_time m2 hq).2
          have := abs_nonneg (p.2 - q.2)
          omega
        have h2 : pastPart t₁ u p = 0 := by
          simp only [pastPart]; split_ifs with h
          · omega
          · rfl
        rw [h1, h2, sub_zero])
    exact sub_eq_zero.1 h
  rw [causalProp, hadv, hret, sub_sub_cancel]

/-- E1, Corollary 11: if `O` depends on `O'` and `supp f ⊆ O`, there is `f'` with
`supp f' ⊆ O'` and `E f' = E f`. -/
theorem exists_causalProp_eq_of_dependent {O O' : Set Point} (hdep : causalIndex.Dependent O O')
    {f : TestFun} (hf : (↑f.support : Set Point) ⊆ O) :
    ∃ f' : TestFun, (↑f'.support : Set Point) ⊆ O' ∧ causalProp m2 f' = causalProp m2 f := by
  obtain ⟨t₁, ht⟩ := hdep _ f.support.finite_toSet hf
  refine ⟨timeSlice m2 f t₁, fun p hp => ?_, causalProp_timeSlice m2 f t₁⟩
  obtain ⟨hs, q, hq, hpq⟩ := timeSlice_support m2 f t₁ hp
  exact ht ⟨⟨q, hq, hpq⟩, hs⟩

end Lattice

end LinearAQFT

end
