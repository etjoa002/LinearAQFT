/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Analysis.LineDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Averages of smooth functions over a compact parameter space

General facts used by the rotation average of stage G (milestone G3), moved here from
`Minkowski/Rotation.lean` in stage H (milestone H2, carried H1 finding 2) under the placement rule:
the partial derivative in the second argument of a function on `V × E`, and averages
`∫ Ψ(ι x, p) dμ(x)` over a compact parameter space, which are smooth and commute with line
derivatives. Namespace `LinearAQFT`.
-/

namespace LinearAQFT

open scoped ContDiff Topology
open MeasureTheory Set Filter Function Metric

/-! ### Averages over a compact parameter space -/

section Average

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ]
  {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] {ι : X → V}

/-- The derivative of `Ψ (v, ·)` at `z = (v, p)`. -/
noncomputable def fderivSnd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : V × E → F)
    (z : V × E) : E →L[ℝ] F :=
  (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inr ℝ V E)

omit [ProperSpace E] in
theorem hasFDerivAt_fderivSnd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ψ : V × E → F}
    (hΨ : ContDiff ℝ 1 Ψ) (v : V) (p : E) :
    HasFDerivAt (fun q => Ψ (v, q)) (fderivSnd Ψ (v, p)) p :=
  ((hΨ.differentiable (by norm_num)) (v, p)).hasFDerivAt.comp p (hasFDerivAt_prodMk_right v p)

omit [ProperSpace E] in
theorem contDiff_fderivSnd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ψ : V × E → F}
    {n : ℕ} (hΨ : ContDiff ℝ (n + 1) Ψ) : ContDiff ℝ n (fderivSnd Ψ) :=
  (hΨ.fderiv_right le_rfl).clm_comp contDiff_const

omit [ProperSpace E] [SecondCountableTopology X] in
/-- A continuous function on a compact space is integrable for a finite measure. -/
theorem integrable_of_continuous_of_compactSpace {F : Type} [NormedAddCommGroup F] {g : X → F}
    (hg : Continuous g) :
    Integrable g μ :=
  integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ)

variable (ι) in
/-- The average `p ↦ ∫ Ψ (ι x, p) dμ(x)`. -/
noncomputable def avg {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : V × E → F)
    (p : E) : F :=
  ∫ x, Ψ (ι x, p) ∂μ

variable (hι : Continuous ι)
include hι

/-- Differentiation of an average under the integral sign. -/
theorem hasFDerivAt_avg {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {Ψ : V × E → F} (hΨ : ContDiff ℝ 1 Ψ) (p₀ : E) :
    HasFDerivAt (avg μ ι Ψ) (avg μ ι (fderivSnd Ψ) p₀) p₀ := by
  have hD : Continuous (fderivSnd Ψ) := (hΨ.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have hc : ∀ p, Continuous fun x => Ψ (ι x, p) := fun p =>
    hΨ.continuous.comp (hι.prodMk continuous_const)
  have hcD : Continuous fun xp : X × E => fderivSnd Ψ (ι xp.1, xp.2) :=
    hD.comp ((hι.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall p₀ 1)).exists_bound_of_continuousOn
    hcD.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun p x => Ψ (ι x, p)) (F' := fun p x => fderivSnd Ψ (ι x, p)) (bound := fun _ => C)
    (ball_mem_nhds p₀ one_pos) (Eventually.of_forall fun p => (hc p).aestronglyMeasurable)
    (integrable_of_continuous_of_compactSpace μ (hc p₀))
    (hD.comp (hι.prodMk continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun x p hp => hC (x, p) ⟨mem_univ _, ball_subset_closedBall hp⟩)
    (integrable_const C) (Eventually.of_forall fun x p _ => hasFDerivAt_fderivSnd hΨ (ι x) p)

/-- Averages of smooth functions are smooth. -/
theorem contDiff_avg_nat : ∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {Ψ : V × E → F}, ContDiff ℝ (n + 1) Ψ → ContDiff ℝ n (avg μ ι Ψ) := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ Ψ hΨ
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p =>
      (hasFDerivAt_avg μ hι (by simpa using hΨ) p).continuousAt
  | succ n ih =>
    intro F _ _ _ Ψ hΨ
    have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by norm_cast; omega)
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨avg μ ι (fderivSnd Ψ), ih ?_, hasFDerivAt_avg μ hι hΨ1⟩
    exact contDiff_fderivSnd (n := n + 1) (by exact_mod_cast hΨ)

theorem contDiff_avg {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {Ψ : V × E → F} (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (avg μ ι Ψ) :=
  contDiff_infty.2 fun n => contDiff_avg_nat μ hι n (hΨ.of_le (by exact_mod_cast le_top))

/-- The line derivative of an average is the average of the line derivatives. -/
theorem lineDeriv_avg {Ψ : V × E → ℝ} (hΨ : ContDiff ℝ 1 Ψ) (p v : E) :
    lineDeriv ℝ (avg μ ι Ψ) p v = avg μ ι (fun z => lineDeriv ℝ (fun q => Ψ (z.1, q)) z.2 v) p := by
  have hD : Continuous (fderivSnd Ψ) := (hΨ.continuous_fderiv one_ne_zero).clm_comp continuous_const
  rw [((hasFDerivAt_avg μ hι hΨ p).hasLineDerivAt v).lineDeriv, avg,
    ContinuousLinearMap.integral_apply (φ := fun x => fderivSnd Ψ (ι x, p))
      (integrable_of_continuous_of_compactSpace μ (hD.comp (hι.prodMk continuous_const)))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact (((hasFDerivAt_fderivSnd hΨ (ι x) p).hasLineDerivAt v).lineDeriv).symm

end Average

section SndDeriv

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

theorem lineDeriv_snd_eq {Ψ : V × E → ℝ} (hΨ : ContDiff ℝ 1 Ψ) (v : E) :
    (fun z : V × E => lineDeriv ℝ (fun q => Ψ (z.1, q)) z.2 v) = fun z => fderivSnd Ψ z v :=
  funext fun z => ((hasFDerivAt_fderivSnd hΨ z.1 z.2).hasLineDerivAt v).lineDeriv

theorem contDiff_lineDeriv_snd {Ψ : V × E → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (v : E) :
    ContDiff ℝ ∞ (fun z : V × E => lineDeriv ℝ (fun q => Ψ (z.1, q)) z.2 v) := by
  rw [lineDeriv_snd_eq (hΨ.of_le (by exact_mod_cast le_top)) v]
  refine contDiff_infty.2 fun n => ?_
  exact (contDiff_fderivSnd (n := n) (hΨ.of_le (by exact_mod_cast le_top))).clm_apply
    contDiff_const

end SndDeriv

end LinearAQFT
