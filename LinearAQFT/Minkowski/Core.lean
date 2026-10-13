/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Radial

/-!
# The core Kirchhoff identity

Stage G, milestone G3 (Theorem 8, Lemma 9, Corollary 10). For `ψ` smooth with compact support,
`∫_{ℝ³} (□ψ)(|y|, y)/|y| dy = 4π ψ(0)`: the kernel `δ(t − |y|)/(4π|y|)` is a fundamental
solution of `□`. Hence `G^± □ f = f` and `□ G^± f = f` for test functions `f`.

## Main results

* `integral_wave_cone` (Theorem 8).
* `wave_comp_reflect` (Lemma 9).
* `gret_waveD`, `gadv_waveD`, `waveF_gret_eq`, `waveF_gadv_eq` (Corollary 10).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology
open MeasureTheory Set Filter Function Metric

/-- The integrand of G3, Theorem 8 is integrable (carried stage-G finding 11). -/
theorem integrable_wave_cone {ψ : Point → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun y : Space => wave ψ (‖y‖, y) / ‖y‖) := by
  have hcb : HasCompactSupport (wave ψ) :=
    hcψ.mono' ((subset_tsupport _).trans (tsupport_wave_subset ψ))
  refine integrable_div_norm (((contDiff_wave hψ).continuous).comp (by fun_prop)) ?_
  refine HasCompactSupport.intro (hcb.image continuous_snd) fun y hy => ?_
  by_contra hne
  exact hy ⟨(‖y‖, y), subset_tsupport _ hne, rfl⟩

/-- G3, Theorem 8, the core identity: `∫_{ℝ³} (□ψ)(|y|, y)/|y| dy = 4π ψ(0)`. -/
theorem integral_wave_cone {ψ : Point → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ∫ y : Space, wave ψ (‖y‖, y) / ‖y‖ = 4 * Real.pi * ψ 0 := by
  have hb : Continuous (wave ψ) := (contDiff_wave hψ).continuous
  have hcb : HasCompactSupport (wave ψ) :=
    hcψ.mono' ((subset_tsupport _).trans (tsupport_wave_subset ψ))
  have ha := contDiff_radialProfile hψ
  have hca := hasCompactSupport_radialProfile hcψ
  set a := radialProfile ψ
  set G : ℝ → ℝ := fun ρ => (partialS (partialS a) (ρ, ρ) - partialR (partialR a) (ρ, ρ) -
    2 / ρ * partialR a (ρ, ρ)) * ρ⁻¹ with hG
  have step1 : ∫ y : Space, wave ψ (‖y‖, y) / ‖y‖ = ∫ y : Space, G ‖y‖ := by
    have h := integral_rotAvg hb hcb (w := fun ρ => ρ⁻¹) locallyIntegrable_inv_norm
    simp only [div_eq_mul_inv]
    rw [h, ← wave_rotAvg hψ]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y = 0
    · simp [hy, hG]
    · have hr : rotAvg ψ = fun q : Point => a (q.1, ‖q.2‖) :=
        funext (rotAvg_eq_radialProfile ψ)
      change wave (rotAvg ψ) (‖y‖, y) * ‖y‖⁻¹ = G ‖y‖
      rw [hr, wave_radial (a := a) ha (‖y‖, y) hy]
  rw [step1, integral_radial]
  have step2 : ∫ ρ in Ioi (0 : ℝ), ρ ^ 2 * G ρ = ∫ ρ in Ioi (0 : ℝ), ρ *
      (partialS (partialS a) (ρ, ρ) - partialR (partialR a) (ρ, ρ) -
        2 / ρ * partialR a (ρ, ρ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    have : ρ ≠ 0 := ne_of_gt hρ
    simp only [hG]
    field_simp
  rw [step2, integral_radial_boundary (a := a) ha hca]
  exact congrArg _ (radialProfile_zero ψ)

/-- G3, Lemma 9: `□` commutes with the maps `q ↦ b + (σ q⁰, τ q⃗)`, `σ, τ = ±1`. -/
theorem wave_comp_reflect {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (b : Point) {σ τ : ℝ}
    (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) :
    wave (fun q : Point => f (b + (σ * q.1, τ • q.2))) =
      fun q : Point => wave f (b + (σ * q.1, τ • q.2)) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast)
  rcases (mul_self_eq_one_iff (a := τ)).1 (by rw [← pow_two]; exact hτ) with h | h
  · subst h
    have := wave_comp_affine hf2 b hσ (LinearIsometryEquiv.refl ℝ Space)
    simpa using this
  · subst h
    have := wave_comp_affine hf2 b hσ (LinearIsometryEquiv.neg ℝ (E := Space))
    simpa using this

/-- `□ψ` for `ψ(s, z) = f(t − s, x − z)`, as used in Corollary 10. -/
theorem wave_comp_sub_left {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (p q : Point) :
    wave (fun q : Point => f (p - q)) q = wave f (p - q) := by
  have e : ∀ q : Point, p - q = p + ((-1) * q.1, (-1 : ℝ) • q.2) := by
    intro q
    ext <;> simp [sub_eq_add_neg]
  simp only [e]
  exact congrFun (wave_comp_reflect hf p (by norm_num) (by norm_num)) q

/-- `□ψ` for `ψ(s, z) = f(t + s, x − z)`, as used in Corollary 10. -/
theorem wave_comp_add_neg {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (p q : Point) :
    wave (fun q : Point => f (p + (q.1, -q.2))) q = wave f (p + (q.1, -q.2)) := by
  have e : ∀ q : Point, p + (q.1, -q.2) = p + (1 * q.1, (-1 : ℝ) • q.2) := by
    intro q
    simp
  simp only [e]
  exact congrFun (wave_comp_reflect hf p (by norm_num) (by norm_num)) q

/-- The homeomorphism `q ↦ p + (q⁰, −q⃗)`. -/
def reflectSpaceAdd (p : Point) : Point ≃ₜ Point :=
  ((Homeomorph.refl ℝ).prodCongr (Homeomorph.neg Space)).trans (Homeomorph.addLeft p)

theorem reflectSpaceAdd_apply (p q : Point) : reflectSpaceAdd p q = p + (q.1, -q.2) := rfl

/-- G3, Corollary 10: `G⁺ P_𝒟 f = f`. -/
theorem gret_waveD (f : TestFun) : gret (waveD f) = incl f := by
  apply Subtype.ext
  funext p
  change kirchhoff coneMeasure (wave f) p = f p
  rw [kirchhoff_coneMeasure_apply (contDiff_wave f.contDiff).continuous]
  set ψ : Point → ℝ := fun q => f (p - q) with hψdef
  have hψ : ContDiff ℝ ∞ ψ := f.contDiff.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := f.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft p)
  have hbox : ∀ y : Space, wave f (p.1 - ‖y‖, p.2 - y) = wave ψ (‖y‖, y) := fun y =>
    (wave_comp_sub_left f.contDiff p (‖y‖, y)).symm
  simp only [hbox]
  have h0 : ψ 0 = f p := by simp [hψdef]
  rw [integral_wave_cone hψ hcψ, h0]
  field_simp

/-- G3, Corollary 10: `G⁻ P_𝒟 f = f`. -/
theorem gadv_waveD (f : TestFun) : gadv (waveD f) = incl f := by
  apply Subtype.ext
  funext p
  change kirchhoff coneMeasurePast (wave f) p = f p
  rw [kirchhoff_coneMeasurePast_apply (contDiff_wave f.contDiff).continuous]
  set ψ : Point → ℝ := fun q => f (p + (q.1, -q.2)) with hψdef
  have hψ : ContDiff ℝ ∞ ψ :=
    f.contDiff.comp (contDiff_const.add (contDiff_fst.prodMk contDiff_snd.neg))
  have hcψ : HasCompactSupport ψ := f.hasCompactSupport.comp_homeomorph (reflectSpaceAdd p)
  have hbox : ∀ y : Space, wave f (p.1 + ‖y‖, p.2 - y) = wave ψ (‖y‖, y) := by
    intro y
    rw [wave_comp_add_neg f.contDiff p (‖y‖, y)]
    congr 1
  simp only [hbox]
  have h0 : ψ 0 = f p := by
    simp only [hψdef]
    congr 1
    ext <;> simp
  rw [integral_wave_cone hψ hcψ, h0]
  field_simp

/-- G3, Corollary 10: `□ G⁺ f = f` (stage F's condition (G6)). -/
theorem waveF_gret_eq (f : TestFun) : waveF (gret f) = incl f := by
  rw [waveF_gret, gret_waveD]

/-- G3, Corollary 10: `□ G⁻ f = f`. -/
theorem waveF_gadv_eq (f : TestFun) : waveF (gadv f) = incl f := by
  rw [waveF_gadv, gadv_waveD]

end LinearAQFT.Minkowski
