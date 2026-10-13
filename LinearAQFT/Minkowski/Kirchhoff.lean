/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Causal
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The Kirchhoff Green operators

Stage G, milestone G2. The retarded and advanced Green operators of the wave operator on `3+1`
Minkowski space, as convolutions with the light-cone measures: `μ⁺` is the image of
`dy/(4π|y|)` under `y ↦ (|y|, y)` and `μ⁻` its image under `c ↦ −c`, and
`(G^± f)(p) = ∫ f(p − c) dμ^±(c)`. Signs: `G⁺` samples `f` in the causal past of `p`, so
`G⁺ f` is supported in the causal future of `supp f` (retarded, programme convention).

## Main results

* `coneMeasure`, `coneMeasurePast`; they are finite on compact sets (G2, Lemma 2).
* `kirchhoff_coneMeasure_apply`, `kirchhoff_coneMeasurePast_apply`: the Kirchhoff formula
  `(G^± f)(t,x) = (1/4π) ∫ f(t ∓ |y|, x − y)/|y| dy` (Proposition 4).
* `contDiff_kirchhoff`, `dirDeriv_kirchhoff`, `wave_kirchhoff`, `gret`, `gadv` (Proposition 5).
* `supp_gret`, `supp_gadv` (Proposition 6); `pairing_gret` (Proposition 7).
* (`Jplus`, `Jminus`, `isClosed_Jplus`, `isClosed_Jminus` are in `Causal.lean`);
  `support_gret`, `support_gadv` (pointwise supports).
* `locallyIntegrable_inv_norm`, `integrable_div_norm`, `integrable_kirchhoff_integrand`
  (the integrand of Proposition 4 is integrable).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Convolution Topology Pointwise
open MeasureTheory Set Filter Function Metric

/-! ### The weight `1/|y|` -/

/-- `1/|y|` is locally integrable on `ℝ³` (the density of G2, Lemma 2). -/
theorem locallyIntegrable_inv_norm : LocallyIntegrable (fun y : Space => ‖y‖⁻¹) := by
  have hball : ∀ R : ℝ, IntegrableOn (fun y : Space => ‖y‖⁻¹) (ball (0 : Space) R) := by
    intro R
    have := (integrableOn_fun_norm_addHaar (μ := (volume : Measure Space))
      (f := fun r : ℝ => r⁻¹) (r := R)).2 ?_
    · simpa using this
    · rw [finrank_euclideanSpace, Fintype.card_fin]
      refine ((continuous_id.continuousOn (s := Icc 0 R)).integrableOn_Icc).mono_set
        Ioo_subset_Icc_self |>.congr_fun ?_ measurableSet_Ioo
      intro y hy
      have hy0 : y ≠ 0 := ne_of_gt hy.1
      simp only [smul_eq_mul, id]
      field_simp
  intro x
  exact ⟨ball 0 (‖x‖ + 1), isOpen_ball.mem_nhds (by simp), hball _⟩

/-- A continuous, compactly supported `g` on `ℝ³` has `g(y)/|y|` integrable. -/
theorem integrable_div_norm {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    Integrable (fun y : Space => g y / ‖y‖) := by
  have h : IntegrableOn (fun y : Space => g y * ‖y‖⁻¹) (tsupport g) :=
    (locallyIntegrable_inv_norm.integrableOn_isCompact hcg).continuousOn_mul hg.continuousOn hcg
  simp_rw [div_eq_mul_inv]
  refine (integrableOn_iff_integrable_of_support_subset fun y hy => ?_).1 h
  exact subset_tsupport _ (left_ne_zero_of_mul hy)

/-! ### The light-cone measures -/

/-- The Kirchhoff weight `1/(4π|y|)` on space (its value `0` at `y = 0` is on a null set). -/
noncomputable def kirchhoffWeight (y : Space) : ENNReal :=
  ENNReal.ofReal (1 / (4 * Real.pi * ‖y‖))

theorem measurable_kirchhoffWeight : Measurable kirchhoffWeight := by
  unfold kirchhoffWeight
  fun_prop

/-- The map `y ↦ (|y|, y)` onto the future light cone. -/
noncomputable def coneMap (y : Space) : Point := (‖y‖, y)

theorem continuous_coneMap : Continuous coneMap := continuous_norm.prodMk continuous_id

/-- G2, Definition 1: the future light-cone measure `μ⁺`. -/
noncomputable def coneMeasure : Measure Point :=
  (volume.withDensity kirchhoffWeight).map coneMap

/-- G2, Definition 1: the past light-cone measure `μ⁻ = (−id)_* μ⁺`. -/
noncomputable def coneMeasurePast : Measure Point :=
  coneMeasure.map Neg.neg

theorem norm_coneMap (y : Space) : ‖coneMap y‖ = ‖y‖ := by
  simp [coneMap, Prod.norm_def]

/-- `∫_{|y|<R} dy/(4π|y|) < ∞`. -/
theorem withDensity_kirchhoffWeight_ball_lt_top (R : ℝ) :
    volume.withDensity kirchhoffWeight (ball (0 : Space) R) < ⊤ := by
  rw [withDensity_apply _ measurableSet_ball]
  have hint : IntegrableOn (fun y : Space => 1 / (4 * Real.pi * ‖y‖)) (ball (0 : Space) R) := by
    have h0 : IntegrableOn (fun y : Space => 1 / (4 * Real.pi) * ‖y‖⁻¹) (ball (0 : Space) R) :=
      ((locallyIntegrable_inv_norm.integrableOn_isCompact (isCompact_closedBall 0 R)).mono_set
        ball_subset_closedBall).const_mul _
    refine IntegrableOn.congr_fun h0 (fun y _ => ?_) measurableSet_ball
    simp only [one_div, mul_inv]
  exact hint.lintegral_lt_top

/-- G2, Lemma 2: `μ⁺` is finite on compact sets. -/
instance : IsFiniteMeasureOnCompacts coneMeasure where
  lt_top_of_isCompact {K} hK := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Point)
    rw [coneMeasure, Measure.map_apply continuous_coneMap.measurable hK.measurableSet]
    refine lt_of_le_of_lt (measure_mono fun y hy => ?_) (withDensity_kirchhoffWeight_ball_lt_top R)
    have := hR hy
    rw [mem_ball_zero_iff, norm_coneMap] at this
    exact mem_ball_zero_iff.2 this

/-- G2, Lemma 2: `μ⁻` is finite on compact sets. -/
instance : IsFiniteMeasureOnCompacts coneMeasurePast where
  lt_top_of_isCompact {K} hK := by
    rw [coneMeasurePast, Measure.map_apply measurable_neg hK.measurableSet]
    exact hK.neg.measure_lt_top

/-! ### The Kirchhoff operators -/

/-- G2, Definition 3: `G^± f = 1 ⋆ f` for `μ^±`, i.e. `(G^± f)(p) = ∫ f(p − c) dμ^±(c)`. -/
noncomputable def kirchhoff (μ : Measure Point) (f : Point → ℝ) : Point → ℝ :=
  (fun _ => (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f

theorem kirchhoff_apply (μ : Measure Point) (f : Point → ℝ) (p : Point) :
    kirchhoff μ f p = ∫ c, f (p - c) ∂μ := by
  simp [kirchhoff, convolution_def]

section Operators

variable (μ : Measure Point) [IsFiniteMeasureOnCompacts μ]

theorem integrable_comp_sub {u : Point → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u)
    (p : Point) : Integrable (fun c => u (p - c)) μ :=
  (hu.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    (hcu.comp_homeomorph (Homeomorph.subLeft p))

theorem kirchhoff_add {u w : Point → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u)
    (hw : Continuous w) (hcw : HasCompactSupport w) :
    kirchhoff μ (u + w) = kirchhoff μ u + kirchhoff μ w := by
  funext p
  simp only [kirchhoff_apply, Pi.add_apply]
  exact integral_add (integrable_comp_sub μ hu hcu p) (integrable_comp_sub μ hw hcw p)

omit [IsFiniteMeasureOnCompacts μ] in
theorem kirchhoff_smul (c : ℝ) (u : Point → ℝ) : kirchhoff μ (c • u) = c • kirchhoff μ u := by
  funext p
  simp only [kirchhoff_apply, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

/-- G2, Proposition 5(a): `G^± f` is smooth. -/
theorem contDiff_kirchhoff {u : Point → ℝ} (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) :
    ContDiff ℝ ∞ (kirchhoff μ u) :=
  hcu.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (locallyIntegrable_const 1) hu

/-- G2, Proposition 5(b): `∂ᵥ (G^± u) = G^± (∂ᵥ u)`, by differentiation under the integral. -/
theorem hasLineDerivAt_kirchhoff {u : Point → ℝ} (hu : ContDiff ℝ ∞ u)
    (hcu : HasCompactSupport u) (v q : Point) :
    HasLineDerivAt ℝ (kirchhoff μ u) (kirchhoff μ (dirDeriv v u) q) q v := by
  have hdu : ContDiff ℝ ∞ (dirDeriv v u) := contDiff_dirDeriv v hu
  have hcdu : HasCompactSupport (dirDeriv v u) := hasCompactSupport_dirDeriv v hcu
  obtain ⟨C, hC⟩ := hdu.continuous.bounded_above_of_compact_support hcdu
  obtain ⟨R, hR⟩ := hcu.isCompact.isBounded.subset_closedBall 0
  set K := closedBall (0 : Point) (‖q‖ + ‖v‖ + R)
  have hK : IsCompact K := isCompact_closedBall _ _
  -- the integrand and its derivative in the parameter `s`
  let F : ℝ → Point → ℝ := fun s c => u (q + s • v - c)
  let F' : ℝ → Point → ℝ := fun s c => dirDeriv v u (q + s • v - c)
  have hsupp : ∀ s ∈ ball (0 : ℝ) 1, ∀ c, c ∉ K → F' s c = 0 := by
    intro s hs c hc
    by_contra hne
    apply hc
    have hmem : q + s • v - c ∈ tsupport u :=
      tsupport_dirDeriv_subset v u (subset_tsupport _ hne)
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff] at h1
    have hs1 : |s| < 1 := by simpa [Real.dist_eq] using hs
    have hsv : ‖s • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [norm_nonneg v, abs_nonneg s]
    rw [mem_closedBall_zero_iff]
    calc ‖c‖ = ‖(q + s • v) - (q + s • v - c)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖q + s • v‖ + ‖q + s • v - c‖ := norm_sub_le _ _
      _ ≤ ‖q‖ + ‖s • v‖ + R := by linarith [norm_add_le q (s • v)]
      _ ≤ ‖q‖ + ‖v‖ + R := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (x₀ := (0 : ℝ)) (bound := K.indicator fun _ => C) (ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun s =>
      (hu.continuous.comp ((continuous_const.add continuous_const).sub
        continuous_id)).aestronglyMeasurable)
    (by simpa [F] using integrable_comp_sub μ hu.continuous hcu q)
    ((hdu.continuous.comp ((continuous_const.add continuous_const).sub
        continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun c s hs => by
      by_cases hc : c ∈ K
      · simp only [indicator_of_mem hc]
        simpa [Real.norm_eq_abs] using hC (q + s • v - c)
      · simp [indicator_of_notMem hc, hsupp s hs c hc])
    ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet)
    (Eventually.of_forall fun c s _ => by
      have hd : HasDerivAt (fun s : ℝ => q + s • v - c) v s := by
        simpa using ((hasDerivAt_id s).smul_const v).const_add q |>.sub_const c
      have hfd := ((hu.differentiable (by simp)) (q + s • v - c)).hasFDerivAt.comp_hasDerivAt s hd
      change HasDerivAt (fun x => u (q + x • v - c)) (dirDeriv v u (q + s • v - c)) s
      rw [dirDeriv, ((hu.differentiable (by simp)) _).lineDeriv_eq_fderiv]
      exact hfd)
  have h2 := key.2
  simp only [F, F', zero_smul, add_zero] at h2
  rw [HasLineDerivAt]
  have hEq : (fun s : ℝ => kirchhoff μ u (q + s • v)) = fun s => ∫ c, u (q + s • v - c) ∂μ := by
    funext s
    rw [kirchhoff_apply]
  rw [hEq, kirchhoff_apply]
  simpa using h2

theorem dirDeriv_kirchhoff {u : Point → ℝ} (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (v : Point) : dirDeriv v (kirchhoff μ u) = kirchhoff μ (dirDeriv v u) :=
  funext fun q => (hasLineDerivAt_kirchhoff μ hu hcu v q).lineDeriv

theorem kirchhoff_sub {u w : Point → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u)
    (hw : Continuous w) (hcw : HasCompactSupport w) :
    kirchhoff μ (u - w) = kirchhoff μ u - kirchhoff μ w := by
  funext p
  simp only [kirchhoff_apply, Pi.sub_apply]
  exact integral_sub (integrable_comp_sub μ hu hcu p) (integrable_comp_sub μ hw hcw p)

theorem kirchhoff_finsetSum {ι : Type*} (s : Finset ι) {u : ι → Point → ℝ}
    (hu : ∀ i, Continuous (u i)) (hcu : ∀ i, HasCompactSupport (u i)) :
    kirchhoff μ (∑ i ∈ s, u i) = ∑ i ∈ s, kirchhoff μ (u i) := by
  funext p
  simp only [kirchhoff_apply, Finset.sum_apply]
  exact integral_finsetSum s fun i _ => integrable_comp_sub μ (hu i) (hcu i) p

/-- G2, Proposition 5(b): `□ G^± u = G^± □ u`. -/
theorem wave_kirchhoff {u : Point → ℝ} (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) :
    wave (kirchhoff μ u) = kirchhoff μ (wave u) := by
  have d1 : ∀ w, ContDiff ℝ ∞ (dirDeriv w u) := fun w => contDiff_dirDeriv w hu
  have c1 : ∀ w, HasCompactSupport (dirDeriv w u) := fun w => hasCompactSupport_dirDeriv w hcu
  have d2 : ∀ w, ContDiff ℝ ∞ (dirDeriv w (dirDeriv w u)) := fun w => contDiff_dirDeriv w (d1 w)
  have c2 : ∀ w, HasCompactSupport (dirDeriv w (dirDeriv w u)) := fun w =>
    hasCompactSupport_dirDeriv w (c1 w)
  have hDD : ∀ w, dirDeriv w (dirDeriv w (kirchhoff μ u)) =
      kirchhoff μ (dirDeriv w (dirDeriv w u)) := fun w => by
    rw [dirDeriv_kirchhoff μ hu hcu, dirDeriv_kirchhoff μ (d1 w) (c1 w)]
  have hsum := kirchhoff_finsetSum μ Finset.univ (u := fun i => dirDeriv (spaceDir i)
    (dirDeriv (spaceDir i) u)) (fun i => (d2 _).continuous) (fun i => c2 _)
  have hcs : HasCompactSupport (∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) u)) := by
    refine hcu.mono' fun p hp => ?_
    have hp' : ∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) u) p ≠ 0 := by
      simpa [Finset.sum_apply] using hp
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
    exact tsupport_dirDeriv_subset _ u (tsupport_dirDeriv_subset _ _ (subset_tsupport _ hi))
  calc wave (kirchhoff μ u)
      = kirchhoff μ (dirDeriv timeDir (dirDeriv timeDir u)) -
          ∑ i, kirchhoff μ (dirDeriv (spaceDir i) (dirDeriv (spaceDir i) u)) := by
        unfold wave
        rw [hDD timeDir]
        congr 1
        exact Finset.sum_congr rfl fun i _ => hDD _
    _ = kirchhoff μ (dirDeriv timeDir (dirDeriv timeDir u)) -
          kirchhoff μ (∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) u)) := by rw [hsum]
    _ = kirchhoff μ (wave u) := by
        have hb : wave u = dirDeriv timeDir (dirDeriv timeDir u) -
            ∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) u) := rfl
        have hcont : Continuous (∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) u)) := by
          rw [Finset.sum_fn]
          exact continuous_finsetSum _ fun i _ => (d2 _).continuous
        rw [hb, kirchhoff_sub μ (d2 _).continuous (c2 _) hcont hcs]

end Operators

/-- `G^± h ≥ 0` for `h ≥ 0`, for every measure. -/
theorem kirchhoff_nonneg (μ : Measure Point) {h : Point → ℝ} (h0 : ∀ q, 0 ≤ h q) (p : Point) :
    0 ≤ kirchhoff μ h p := by
  rw [kirchhoff_apply]
  exact integral_nonneg fun c => h0 _


/-! ### The Kirchhoff formula -/

/-- Integrating against `μ⁺` is integrating over space with the weight `1/(4π|y|)`. -/
theorem integral_coneMeasure {g : Point → ℝ} (hg : Continuous g) :
    ∫ c, g c ∂coneMeasure = ∫ y : Space, g (coneMap y) / (4 * Real.pi * ‖y‖) := by
  rw [coneMeasure, integral_map continuous_coneMap.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul measurable_kirchhoffWeight
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  have h0 : (0 : ℝ) ≤ 1 / (4 * Real.pi * ‖y‖) := by positivity
  rw [kirchhoffWeight, ENNReal.toReal_ofReal h0, smul_eq_mul]
  ring

/-- G2, Proposition 4: `(G⁺ f)(t,x) = (1/4π) ∫ f(t − |y|, x − y)/|y| dy`. -/
theorem kirchhoff_coneMeasure_apply {f : Point → ℝ} (hf : Continuous f) (p : Point) :
    kirchhoff coneMeasure f p =
      (1 / (4 * Real.pi)) * ∫ y : Space, f (p.1 - ‖y‖, p.2 - y) / ‖y‖ := by
  rw [kirchhoff_apply, integral_coneMeasure (g := fun c => f (p - c)) (by fun_prop),
    ← integral_const_mul]
  congr 1
  funext y
  have : p - coneMap y = (p.1 - ‖y‖, p.2 - y) := rfl
  rw [this]
  ring

/-- G2, Proposition 4: the Kirchhoff integrands `f(t ∓ |y|, x − y)/|y|` are integrable (carried
stage-G finding 5). -/
theorem integrable_kirchhoff_integrand {f : Point → ℝ} (hf : Continuous f)
    (hcf : HasCompactSupport f) (p : Point) (s : ℝ) :
    Integrable (fun y : Space => f (p.1 + s * ‖y‖, p.2 - y) / ‖y‖) := by
  refine integrable_div_norm (hf.comp (by fun_prop)) ?_
  have hK : IsCompact ((fun z : Space => p.2 - z) '' (Prod.snd '' tsupport f)) :=
    (hcf.image continuous_snd).image (by fun_prop)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  exact hy ⟨p.2 - y, ⟨(p.1 + s * ‖y‖, p.2 - y), subset_tsupport _ hne, rfl⟩, by simp⟩

/-- G2, Proposition 4: `(G⁻ f)(t,x) = (1/4π) ∫ f(t + |y|, x − y)/|y| dy`. -/
theorem kirchhoff_coneMeasurePast_apply {f : Point → ℝ} (hf : Continuous f) (p : Point) :
    kirchhoff coneMeasurePast f p =
      (1 / (4 * Real.pi)) * ∫ y : Space, f (p.1 + ‖y‖, p.2 - y) / ‖y‖ := by
  have hsub : ∫ c, f (p - c) ∂coneMeasurePast = ∫ c, f (p + c) ∂coneMeasure := by
    rw [coneMeasurePast, integral_map measurable_neg.aemeasurable
      (show Continuous fun c => f (p - c) by fun_prop).aestronglyMeasurable]
    simp [sub_neg_eq_add]
  rw [kirchhoff_apply, hsub, integral_coneMeasure (g := fun c => f (p + c)) (by fun_prop),
    ← integral_const_mul,
    ← integral_neg_eq_self (fun y : Space => 1 / (4 * Real.pi) * (f (p.1 + ‖y‖, p.2 - y) / ‖y‖))]
  congr 1
  funext y
  have : p + coneMap y = (p.1 + ‖y‖, p.2 + y) := rfl
  rw [this, norm_neg, sub_neg_eq_add]
  ring

/-! ### The Green operators as linear maps -/

/-- G2, Proposition 5: the retarded Green operator `G⁺ : 𝒟 → 𝓕`. -/
noncomputable def gret : TestFun →ₗ[ℝ] Fn where
  toFun f := ⟨kirchhoff coneMeasure f,
    contDiff_kirchhoff coneMeasure f.contDiff f.hasCompactSupport⟩
  map_add' f g := Subtype.ext (kirchhoff_add coneMeasure f.continuous f.hasCompactSupport
    g.continuous g.hasCompactSupport)
  map_smul' c f := Subtype.ext (kirchhoff_smul coneMeasure c f)

/-- G2, Proposition 5: the advanced Green operator `G⁻ : 𝒟 → 𝓕`. -/
noncomputable def gadv : TestFun →ₗ[ℝ] Fn where
  toFun f := ⟨kirchhoff coneMeasurePast f,
    contDiff_kirchhoff coneMeasurePast f.contDiff f.hasCompactSupport⟩
  map_add' f g := Subtype.ext (kirchhoff_add coneMeasurePast f.continuous f.hasCompactSupport
    g.continuous g.hasCompactSupport)
  map_smul' c f := Subtype.ext (kirchhoff_smul coneMeasurePast c f)

@[simp] theorem gret_apply (f : TestFun) : (gret f : Point → ℝ) = kirchhoff coneMeasure f := rfl
@[simp] theorem gadv_apply (f : TestFun) :
    (gadv f : Point → ℝ) = kirchhoff coneMeasurePast f := rfl

/-- G2, Proposition 5(b): `□ G^± f = G^± P_𝒟 f`. -/
theorem waveF_gret (f : TestFun) : waveF (gret f) = gret (waveD f) :=
  Subtype.ext (wave_kirchhoff coneMeasure f.contDiff f.hasCompactSupport)

theorem waveF_gadv (f : TestFun) : waveF (gadv f) = gadv (waveD f) :=
  Subtype.ext (wave_kirchhoff coneMeasurePast f.contDiff f.hasCompactSupport)

/-! ### Supports -/

/-- `G⁺ f` vanishes outside `J⁺(supp f)`. -/
theorem support_gret (f : TestFun) :
    Function.support (gret f : Point → ℝ) ⊆ Jplus (supp (incl f)) := by
  intro q hq
  by_contra hn
  apply hq
  change kirchhoff coneMeasure f q = 0
  have hz : ∀ y : Space, f (q.1 - ‖y‖, q.2 - y) = 0 := by
    intro y
    by_contra hy
    exact hn ⟨(q.1 - ‖y‖, q.2 - y), support_subset_supp (incl f) hy, by simp [causalLE]⟩
  rw [kirchhoff_coneMeasure_apply f.continuous]
  simp [hz]

/-- `G⁻ f` vanishes outside `J⁻(supp f)`. -/
theorem support_gadv (f : TestFun) :
    Function.support (gadv f : Point → ℝ) ⊆ Jminus (supp (incl f)) := by
  intro q hq
  by_contra hn
  apply hq
  change kirchhoff coneMeasurePast f q = 0
  have hz : ∀ y : Space, f (q.1 + ‖y‖, q.2 - y) = 0 := by
    intro y
    by_contra hy
    exact hn ⟨(q.1 + ‖y‖, q.2 - y), support_subset_supp (incl f) hy, by simp [causalLE]⟩
  rw [kirchhoff_coneMeasurePast_apply f.continuous]
  simp [hz]

/-- G2, Proposition 6: `supp G⁺ f ⊆ J⁺(supp f)` (closed supports). -/
theorem supp_gret (f : TestFun) :
    supp (gret f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q} :=
  closure_minimal (support_gret f) (isClosed_Jplus f.hasCompactSupport)

/-- G2, Proposition 6: `supp G⁻ f ⊆ J⁻(supp f)` (closed supports). -/
theorem supp_gadv (f : TestFun) :
    supp (gadv f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p} :=
  closure_minimal (support_gadv f) (isClosed_Jminus f.hasCompactSupport)

/-! ### Formal adjointness -/

theorem hasCompactSupport_mul_sub {f g : Point → ℝ} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) :
    HasCompactSupport (fun pc : Point × Point => f pc.1 * g (pc.1 - pc.2)) := by
  have hK : IsCompact ((fun x : Point × Point => x.1 - x.2) '' (tsupport f ×ˢ tsupport g)) :=
    (hf.isCompact.prod hg.isCompact).image continuous_sub
  refine HasCompactSupport.intro (hf.isCompact.prod hK) ?_
  intro pc hpc
  by_contra hne
  apply hpc
  have h1 : f pc.1 ≠ 0 := left_ne_zero_of_mul hne
  have h2 : g (pc.1 - pc.2) ≠ 0 := right_ne_zero_of_mul hne
  refine ⟨subset_tsupport _ h1, ?_⟩
  exact ⟨(pc.1, pc.1 - pc.2), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, by simp⟩

theorem hasCompactSupport_mul_add {f g : Point → ℝ} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) :
    HasCompactSupport (fun qc : Point × Point => g qc.1 * f (qc.1 + qc.2)) := by
  have hK : IsCompact ((fun x : Point × Point => x.1 - x.2) '' (tsupport f ×ˢ tsupport g)) :=
    (hf.isCompact.prod hg.isCompact).image continuous_sub
  refine HasCompactSupport.intro (hg.isCompact.prod hK) ?_
  intro qc hqc
  by_contra hne
  apply hqc
  have h1 : g qc.1 ≠ 0 := left_ne_zero_of_mul hne
  have h2 : f (qc.1 + qc.2) ≠ 0 := right_ne_zero_of_mul hne
  refine ⟨subset_tsupport _ h1, ?_⟩
  exact ⟨(qc.1 + qc.2, qc.1), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩

/-- G2, Proposition 7: formal adjointness `⟨f, G⁺ g⟩ = ⟨g, G⁻ f⟩`. -/
theorem pairing_gret (f g : TestFun) : pairing f (gret g) = pairing g (gadv f) := by
  change ∫ p, f p * kirchhoff coneMeasure g p = ∫ q, g q * kirchhoff coneMeasurePast f q
  have hL : ∀ p, f p * kirchhoff coneMeasure g p = ∫ c, f p * g (p - c) ∂coneMeasure :=
    fun p => by rw [kirchhoff_apply, integral_const_mul]
  have hR : ∀ q, g q * kirchhoff coneMeasurePast f q = ∫ c, g q * f (q + c) ∂coneMeasure := by
    intro q
    have hfc : Continuous fun c => f (q - c) :=
      f.continuous.comp (continuous_const.sub continuous_id)
    rw [kirchhoff_apply, coneMeasurePast, integral_map measurable_neg.aemeasurable
      hfc.aestronglyMeasurable, ← integral_const_mul]
    simp [sub_neg_eq_add]
  simp_rw [hL, hR]
  have hi1 : Integrable (uncurry fun p c => f p * g (p - c)) (volume.prod coneMeasure) :=
    ((f.continuous.comp continuous_fst).mul (g.continuous.comp
      (continuous_fst.sub continuous_snd))).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_sub f.hasCompactSupport g.hasCompactSupport)
  have hi2 : Integrable (uncurry fun q c => g q * f (q + c)) (volume.prod coneMeasure) :=
    ((g.continuous.comp continuous_fst).mul (f.continuous.comp
      (continuous_fst.add continuous_snd))).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_add f.hasCompactSupport g.hasCompactSupport)
  rw [integral_integral_swap hi1, integral_integral_swap hi2]
  congr 1
  funext c
  rw [← integral_add_right_eq_self (fun p => f p * g (p - c)) c]
  congr 1
  funext q
  rw [add_sub_cancel_right, mul_comm]

end LinearAQFT.Minkowski
