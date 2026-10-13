/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Analysis.LineDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Calculus on the line and the plane

General facts used by the Minkowski files, moved here from `Minkowski/Radial.lean`,
`Minkowski/Extension.lean`, `Minkowski/Series.lean` and `Minkowski/Cutoff.lean` in the closing
pass (30 Sep 2026) under the placement rule. Namespace `LinearAQFT`.

* `partialS`, `partialR`, `partialR_partialS`, `hasDerivAt_diag`: partial derivatives of a
  profile on `ℝ²` and the chain rule along the diagonal.
* `integral_Ioi_deriv_eq_neg`, `eventually_diag_eq_zero`: the boundary term on a half-line.
* `integral_mul_sub_pow`: the Beta integral `∫₀^τ ρ (τ − ρ)ⁿ dρ = τⁿ⁺² / ((n + 1)(n + 2))`.
* `summable_cosh_series`: the series of `cosh`.
* `mem_closure_of_ray`: a ray into a set ends in its closure.
-/

namespace LinearAQFT

open scoped ContDiff Topology
open MeasureTheory Set Filter Function Metric

/-- `∂ₛ a`, the derivative in the first variable. -/
noncomputable def partialS (a : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := lineDeriv ℝ a z (1, 0)

/-- `∂_ρ a`, the derivative in the second variable. -/
noncomputable def partialR (a : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := lineDeriv ℝ a z (0, 1)

theorem contDiff_partialS {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (partialS a) :=
  contDiff_lineDeriv ha _

theorem contDiff_partialR {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (partialR a) :=
  contDiff_lineDeriv ha _

/-- `∂_ρ ∂ₛ a = ∂ₛ ∂_ρ a`. -/
theorem partialR_partialS {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (z : ℝ × ℝ) :
    partialR (partialS a) z = partialS (partialR a) z :=
  lineDeriv_lineDeriv_comm (ha.of_le (by norm_cast)) z _ _

/-- The chain rule along the diagonal: `d/dρ F(ρ, ρ) = (∂ₛ F + ∂_ρ F)(ρ, ρ)`. -/
theorem hasDerivAt_diag {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (ρ : ℝ) :
    HasDerivAt (fun x => F (x, x)) (partialS F (ρ, ρ) + partialR F (ρ, ρ)) ρ := by
  have hdiag : HasDerivAt (fun x : ℝ => (x, x)) ((1 : ℝ), (1 : ℝ)) ρ :=
    (hasDerivAt_id' ρ).prodMk (hasDerivAt_id' ρ)
  have hd := HasFDerivAt.comp_hasDerivAt (f := fun x : ℝ => (x, x)) ρ
    (hF.differentiable (by norm_num) (ρ, ρ)).hasFDerivAt hdiag
  have e : ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) := by simp
  simp only [comp_def] at hd
  rw [e, map_add] at hd
  rw [partialS, partialR, (hF.differentiable (by norm_num) (ρ, ρ)).lineDeriv_eq_fderiv,
    (hF.differentiable (by norm_num) (ρ, ρ)).lineDeriv_eq_fderiv]
  exact hd

theorem integral_Ioi_deriv_eq_neg {w w' : ℝ → ℝ} (hcont : ContinuousWithinAt w (Ici 0) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt w (w' x) x) (hint : IntegrableOn w' (Ioi 0))
    (hzero : ∀ᶠ x in atTop, w x = 0) : ∫ x in Ioi (0 : ℝ), w' x = -w 0 := by
  have hlim : Tendsto w atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim, zero_sub]

/-- Outside a ball containing the support, the profile and its derivatives vanish on the
diagonal. -/
theorem eventually_diag_eq_zero {F : ℝ × ℝ → ℝ} (hF : HasCompactSupport F) :
    ∀ᶠ x in atTop, (x, x) ∉ tsupport F := by
  obtain ⟨R, hR⟩ := hF.isCompact.isBounded.subset_closedBall 0
  filter_upwards [eventually_gt_atTop R, eventually_gt_atTop 0] with x hx hx0 hmem
  have h := hR hmem
  rw [mem_closedBall_zero_iff] at h
  simp [Prod.norm_def, abs_of_pos hx0] at h
  linarith

/-- The Beta integral (used in H2, Lemma 5) `∫₀^τ ρ (τ − ρ)ⁿ dρ = τⁿ⁺² / ((n + 1)(n + 2))`. -/
theorem integral_mul_sub_pow (τ : ℝ) (n : ℕ) :
    ∫ ρ in (0 : ℝ)..τ, ρ * (τ - ρ) ^ n = τ ^ (n + 2) / ((n + 1) * (n + 2)) := by
  have h1 : ∫ ρ in (0 : ℝ)..τ, ρ * (τ - ρ) ^ n = ∫ σ in (0 : ℝ)..τ, (τ - σ) * σ ^ n := by
    have := intervalIntegral.integral_comp_sub_left (fun σ => (τ - σ) * σ ^ n) (a := 0) (b := τ) τ
    simp only [sub_sub_cancel, sub_self, sub_zero] at this
    exact this
  have h2 : ∫ σ in (0 : ℝ)..τ, (τ - σ) * σ ^ n =
      τ * (∫ σ in (0 : ℝ)..τ, σ ^ n) - ∫ σ in (0 : ℝ)..τ, σ ^ (n + 1) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · congr 1
      funext σ
      ring
    · exact (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
    · exact (continuous_pow (n + 1)).intervalIntegrable _ _
  rw [h1, h2, integral_pow, integral_pow]
  push_cast
  field_simp
  ring

/-- The dominating series is summable. -/
theorem summable_cosh_series (x : ℝ) :
    Summable fun k : ℕ => x ^ (2 * k) / ((2 * k).factorial : ℝ) :=
  (Real.hasSum_cosh x).summable

/-- A point that is the limit of a ray `q + s v`, `s > 0`, inside `W` is in the closure of `W`. -/
theorem mem_closure_of_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} {q v : E}
    (h : ∀ s : ℝ, 0 < s → q + s • v ∈ W) : q ∈ closure W := by
  have ht : Tendsto (fun s : ℝ => q + s • v) (𝓝[>] 0) (𝓝 q) := by
    have : Continuous fun s : ℝ => q + s • v := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

end LinearAQFT
