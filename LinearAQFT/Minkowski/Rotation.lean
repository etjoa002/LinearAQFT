/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Kirchhoff
import LinearAQFT.Minkowski.Wave
import LinearAQFT.Analysis.Average
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Rotations and the rotation average

Stage G, milestone G3 (Definition 1, Lemmas 2 and 3, Proposition 4). Second derivatives along
lines; `□` commutes with the maps `q ↦ b + (σ q⁰, L q⃗)` for `σ = ±1` and `L` a linear isometry
of space; the rotation group `O(3)` (the unitary operators on `ℝ³`), compact, with its Haar
probability measure; and the rotation average
`(Aψ)(s, y) = ∫ ψ(s, R⁻¹ y) dμ(R)`, which is smooth, radial, commutes with `□` and leaves
integrals against radial weights unchanged.

## Main results

* (`wave_comp_affine` is in `Wave.lean`.)
* `O3`, `rotHaar`, `rotHaar_univ` (Definition 1); the `CompactSpace` instance (Lemma 2).
* `exists_rot_eq` (Lemma 3).
* `rotAvg`, `rotAvg_rot`, `contDiff_rotAvg`, `wave_rotAvg`, `integral_rotAvg` (Proposition 4).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology InnerProductSpace
open MeasureTheory Set Filter Function Metric

section AverageBox

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : X → V}

/-- `□` of an average is the average of `□`. -/
theorem wave_avg (hι : Continuous ι) {Ψ : V × Point → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    wave (avg μ ι Ψ) = avg μ ι (fun z => wave (fun q => Ψ (z.1, q)) z.2) := by
  have h1 : ∀ {Φ : V × Point → ℝ}, ContDiff ℝ ∞ Φ → ∀ v : Point,
      dirDeriv v (avg μ ι Φ) = avg μ ι (fun z => lineDeriv ℝ (fun q => Φ (z.1, q)) z.2 v) :=
    fun hΦ v => funext fun p => lineDeriv_avg μ hι (hΦ.of_le (by exact_mod_cast le_top)) p v
  have h2 : ∀ v : Point, dirDeriv v (dirDeriv v (avg μ ι Ψ)) =
      avg μ ι (fun z => dirDeriv v (dirDeriv v (fun q => Ψ (z.1, q))) z.2) := by
    intro v
    rw [h1 hΨ v, h1 (contDiff_lineDeriv_snd hΨ v) v]
    rfl
  have hc : ∀ v : Point, Continuous fun z : V × Point =>
      dirDeriv v (dirDeriv v (fun q => Ψ (z.1, q))) z.2 := fun v =>
    (contDiff_lineDeriv_snd (contDiff_lineDeriv_snd hΨ v) v).continuous
  have hI : ∀ (v : Point) (p : Point), Integrable (fun x =>
      dirDeriv v (dirDeriv v (fun q => Ψ ((ι x), q))) p) μ := fun v p =>
    integrable_of_continuous_of_compactSpace μ ((hc v).comp (hι.prodMk continuous_const))
  funext p
  simp only [wave, Pi.sub_apply, Finset.sum_apply, h2, avg]
  rw [← integral_finsetSum _ fun i _ => hI _ p, ← integral_sub (hI _ p)
    (integrable_finsetSum _ fun i _ => hI _ p)]

end AverageBox

/-! ### The rotation group -/

/-- The adjoint is continuous (Mathlib's instance for normed star groups; stated here so that
instance search finds it for `Space →L[ℝ] Space`). -/
instance : ContinuousStar (Space →L[ℝ] Space) := NormedStarGroup.to_continuousStar

/-- G3, Definition 1: the orthogonal group `O(3)`, the unitary operators on `ℝ³`. -/
noncomputable abbrev O3 := unitary (Space →L[ℝ] Space)

/-- G3, Lemma 2: `O(3)` is compact (closed and bounded, of norm `1`). -/
instance compactSpace_O3 : CompactSpace O3 := by
  refine isCompact_iff_compactSpace.1 ?_
  refine Metric.isCompact_of_isClosed_isBounded isClosed_unitary ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun U hU => ?_⟩
  rw [mem_closedBall_zero_iff, CStarRing.norm_of_mem_unitary hU]

/-- G3, Definition 1: the Haar probability measure on `O(3)`. -/
noncomputable def rotHaar : Measure O3 :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts O3)

/-- G3, Definition 1: `μ_O(O(3)) = 1`. -/
theorem rotHaar_univ : rotHaar univ = 1 := by
  rw [rotHaar, ← TopologicalSpace.PositiveCompacts.coe_top]
  exact Measure.haarMeasure_self

instance : IsProbabilityMeasure rotHaar := ⟨rotHaar_univ⟩

instance : rotHaar.IsMulLeftInvariant := by
  unfold rotHaar
  infer_instance

/-- G3, Definition 1: left invariance, `∫ F(QR) dμ(R) = ∫ F(R) dμ(R)`. -/
theorem integral_rotHaar_mul_left (Q : O3) (F : O3 → ℝ) :
    ∫ R, F (Q * R) ∂rotHaar = ∫ R, F R ∂rotHaar :=
  integral_mul_left_eq_self F Q

/-- The action of a rotation on space. -/
noncomputable def rot (R : O3) : Space ≃ₗᵢ[ℝ] Space := Unitary.linearIsometryEquiv R

theorem rot_mul (R Q : O3) (y : Space) : rot (R * Q) y = rot R (rot Q y) := by
  simp [rot, map_mul, LinearIsometryEquiv.coe_mul]

/-- G3, Lemma 3: rotations act transitively on spheres (a reflection maps `y'` to `y`). -/
theorem exists_rot_eq {y y' : Space} (h : ‖y‖ = ‖y'‖) : ∃ Q : O3, rot Q y' = y := by
  refine ⟨Unitary.linearIsometryEquiv.symm (Submodule.reflection (ℝ ∙ (y' - y))ᗮ), ?_⟩
  simp only [rot, MulEquiv.apply_symm_apply]
  exact Submodule.reflection_sub h.symm

theorem continuous_rot_inv : Continuous fun R : O3 => ((R⁻¹ : O3) : Space →L[ℝ] Space) :=
  continuous_subtype_val.comp continuous_inv

/-! ### The rotation average -/

/-- G3, Definition 1: the rotation average `(Aψ)(s, y) = ∫ ψ(s, R⁻¹ y) dμ(R)`. -/
noncomputable def rotAvg (ψ : Point → ℝ) (p : Point) : ℝ :=
  ∫ R, ψ (p.1, rot R⁻¹ p.2) ∂rotHaar

/-- The integrand of the rotation average, as a function of the operator and the point. -/
def rotIntegrand (ψ : Point → ℝ) (z : (Space →L[ℝ] Space) × Point) : ℝ :=
  ψ (z.2.1, z.1 z.2.2)

theorem rotAvg_eq_avg (ψ : Point → ℝ) :
    rotAvg ψ = avg rotHaar (fun R : O3 => ((R⁻¹ : O3) : Space →L[ℝ] Space)) (rotIntegrand ψ) :=
  rfl

theorem contDiff_rotIntegrand {ψ : Point → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (rotIntegrand ψ) :=
  hψ.comp ((contDiff_snd.fst).prodMk (contDiff_fst.clm_apply contDiff_snd.snd))

/-- G3, Proposition 4(a): `Aψ` is rotation invariant. -/
theorem rotAvg_rot (ψ : Point → ℝ) (Q : O3) (p : Point) :
    rotAvg ψ (p.1, rot Q p.2) = rotAvg ψ p := by
  unfold rotAvg
  rw [← integral_rotHaar_mul_left Q]
  refine integral_congr_ae (Eventually.of_forall fun R => ?_)
  simp only
  rw [← rot_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

/-- G3, Proposition 4(b): `Aψ` is smooth. -/
theorem contDiff_rotAvg {ψ : Point → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (rotAvg ψ) := by
  rw [rotAvg_eq_avg]
  exact contDiff_avg rotHaar continuous_rot_inv (contDiff_rotIntegrand hψ)

/-- G3, Proposition 4(b): `□ Aψ = A □ψ`. -/
theorem wave_rotAvg {ψ : Point → ℝ} (hψ : ContDiff ℝ ∞ ψ) : wave (rotAvg ψ) = rotAvg (wave ψ) := by
  rw [rotAvg_eq_avg, wave_avg rotHaar continuous_rot_inv (contDiff_rotIntegrand hψ)]
  funext p
  refine integral_congr_ae (Eventually.of_forall fun R => ?_)
  have h := wave_comp_affine (hψ.of_le (by norm_cast)) 0 (σ := 1) (by norm_num)
    (rot R⁻¹)
  simp only [zero_add, one_mul] at h
  exact congrFun h p

/-- G3, Proposition 4(c): averaging does not change integrals against radial weights. -/
theorem integral_rotAvg {F : Point → ℝ} (hF : Continuous F) (hcF : HasCompactSupport F)
    {w : ℝ → ℝ} (hw : LocallyIntegrable (fun y : Space => w ‖y‖)) :
    ∫ y : Space, F (‖y‖, y) * w ‖y‖ = ∫ y : Space, rotAvg F (‖y‖, y) * w ‖y‖ := by
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hcF
  obtain ⟨r, hr⟩ := hcF.isCompact.isBounded.subset_closedBall 0
  set g : Space → ℝ := fun y => C * ‖(closedBall (0 : Space) r).indicator (fun y => w ‖y‖) y‖
  have hg : Integrable g :=
    (((hw.integrableOn_isCompact (isCompact_closedBall 0 r)).integrable_indicator
      measurableSet_closedBall).norm).const_mul C
  have hcont : Continuous fun yR : Space × O3 => F (‖yR.1‖, rot yR.2⁻¹ yR.1) :=
    hF.comp ((continuous_norm.comp continuous_fst).prodMk
      ((continuous_rot_inv.comp continuous_snd).clm_apply continuous_fst))
  have hint : Integrable (uncurry fun (y : Space) (R : O3) => F (‖y‖, rot R⁻¹ y) * w ‖y‖)
      ((volume : Measure Space).prod rotHaar) := by
    refine (hg.comp_fst rotHaar).mono' (hcont.aestronglyMeasurable.mul
      hw.aestronglyMeasurable.comp_fst) (Eventually.of_forall fun yR => ?_)
    simp only [uncurry, g]
    by_cases hy : yR.1 ∈ closedBall (0 : Space) r
    · rw [indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · have h0 : F (‖yR.1‖, rot yR.2⁻¹ yR.1) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
        have h1 := hr hmem
        rw [mem_closedBall_zero_iff] at h1 ⊢
        simpa using h1
      simp [h0, indicator_of_notMem hy]
  have hR : ∀ R : O3, ∫ y : Space, F (‖y‖, rot R⁻¹ y) * w ‖y‖ =
      ∫ y : Space, F (‖y‖, y) * w ‖y‖ := by
    intro R
    have hmp := (rot R⁻¹).measurePreserving
    have e : (fun y : Space => F (‖y‖, rot R⁻¹ y) * w ‖y‖) =
        fun y => (fun z : Space => F (‖z‖, z) * w ‖z‖) (rot R⁻¹ y) := by
      funext y
      simp
    rw [e]
    exact hmp.integral_comp (rot R⁻¹).toHomeomorph.measurableEmbedding
      (fun z : Space => F (‖z‖, z) * w ‖z‖)
  calc ∫ y : Space, F (‖y‖, y) * w ‖y‖
      = ∫ R : O3, ∫ y : Space, F (‖y‖, rot R⁻¹ y) * w ‖y‖ ∂volume ∂rotHaar := by
        simp [hR]
    _ = ∫ y : Space, ∫ R : O3, F (‖y‖, rot R⁻¹ y) * w ‖y‖ ∂rotHaar := by
        rw [integral_integral_swap hint]
    _ = ∫ y : Space, rotAvg F (‖y‖, y) * w ‖y‖ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [rotAvg]
        rw [integral_mul_const]

/-! ### The radial profile -/

/-- The first unit vector of space. -/
noncomputable def unitX : Space := EuclideanSpace.single 0 1

theorem norm_unitX : ‖unitX‖ = 1 := by
  simp [unitX]

/-- G3, Proposition 4(a): the radial profile `a(s, ρ) = (Aψ)(s, ρ e₁)`. -/
noncomputable def radialProfile (ψ : Point → ℝ) (z : ℝ × ℝ) : ℝ := rotAvg ψ (z.1, z.2 • unitX)

/-- G3, Proposition 4(a): `(Aψ)(s, y) = a(s, |y|)`. -/
theorem rotAvg_eq_radialProfile (ψ : Point → ℝ) (p : Point) :
    rotAvg ψ p = radialProfile ψ (p.1, ‖p.2‖) := by
  obtain ⟨Q, hQ⟩ := exists_rot_eq (y := p.2) (y' := ‖p.2‖ • unitX)
    (by rw [norm_smul, norm_unitX, mul_one, norm_norm])
  calc rotAvg ψ p = rotAvg ψ (p.1, rot Q (‖p.2‖ • unitX)) := by rw [hQ]
    _ = radialProfile ψ (p.1, ‖p.2‖) := rotAvg_rot ψ Q (p.1, ‖p.2‖ • unitX)

/-- G3, Proposition 4(a): `a(0, 0) = ψ(0)`. -/
theorem radialProfile_zero (ψ : Point → ℝ) : radialProfile ψ (0, 0) = ψ 0 := by
  simp [radialProfile, rotAvg]
  rfl

/-- G3, Proposition 4(b): the profile is smooth. -/
theorem contDiff_radialProfile {ψ : Point → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (radialProfile ψ) :=
  (contDiff_rotAvg hψ).comp (contDiff_fst.prodMk (contDiff_snd.smul contDiff_const))

/-- The profile of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_radialProfile {ψ : Point → ℝ} (hcψ : HasCompactSupport ψ) :
    HasCompactSupport (radialProfile ψ) := by
  obtain ⟨r, hr⟩ := hcψ.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) r) fun z hz => ?_
  simp only [radialProfile, rotAvg]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun R => ?_)
  refine image_eq_zero_of_notMem_tsupport fun hmem => hz ?_
  have h1 := hr hmem
  rw [mem_closedBall_zero_iff] at h1 ⊢
  simpa [Prod.norm_def, norm_smul, norm_unitX] using h1

end LinearAQFT.Minkowski
