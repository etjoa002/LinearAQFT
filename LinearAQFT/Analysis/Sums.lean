/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Finite sums with compact support, and integrals of dominated series

General facts used by the series `G_μ^±` of stage H (milestone H3), moved here from
`Minkowski/Series.lean` in milestone H4 (carried H3 finding 1) under the placement rule: a finite
sum of compactly supported functions is compactly supported (now Mathlib's
`HasCompactSupport.finset_sum`), and an integral against a continuous,
compactly supported weight may be exchanged with a series of continuous functions that is bounded,
on the support of the weight, by a summable sequence. Namespace `LinearAQFT`.
-/

namespace LinearAQFT

open MeasureTheory Set Function

/-- Exchanging an integral against a continuous, compactly supported weight `w` with a series
`Σ_k a_k` of continuous functions bounded on `supp w` by a summable sequence `B`. -/
theorem integral_mul_tsum_eq {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {w : X → ℝ}
    (hw : Continuous w) (hcw : HasCompactSupport w) {a : ℕ → X → ℝ} (ha : ∀ k, Continuous (a k))
    {B : ℕ → ℝ} (hB : Summable B) (hbd : ∀ k p, p ∈ tsupport w → |a k p| ≤ B k) :
    ∫ p, w p * ∑' k, a k p ∂μ = ∑' k, ∫ p, w p * a k p ∂μ := by
  have hint : ∀ k, Integrable (fun p => w p * a k p) μ := fun k =>
    (hw.mul (ha k)).integrable_of_hasCompactSupport hcw.mul_right
  have hwi : Integrable (fun p => |w p|) μ :=
    hw.abs.integrable_of_hasCompactSupport hcw.abs
  have hle : ∀ k, ∫ p, ‖w p * a k p‖ ∂μ ≤ (∫ p, |w p| ∂μ) * B k := by
    intro k
    rw [← integral_mul_const]
    refine integral_mono (hint k).norm (hwi.mul_const _) fun p => ?_
    simp only [norm_mul, Real.norm_eq_abs]
    by_cases hp : p ∈ tsupport w
    · exact mul_le_mul_of_nonneg_left (hbd k p hp) (abs_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hp]
  have hsum : Summable fun k => ∫ p, ‖w p * a k p‖ ∂μ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hle
      (hB.mul_left _)
  calc ∫ p, w p * ∑' k, a k p ∂μ = ∫ p, ∑' k, w p * a k p ∂μ := by
        congr 1
        funext p
        exact tsum_mul_left.symm
    _ = ∑' k, ∫ p, w p * a k p ∂μ := (integral_tsum_of_summable_integral_norm hint hsum).symm

end LinearAQFT
