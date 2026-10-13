/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Rotation
import LinearAQFT.Analysis.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Radial calculus

Stage G, milestone G3 (Lemmas 5, 6 and 7). For a profile `a(s, ρ)` on `ℝ²`, with partial
derivatives `a_s`, `a_ρ` (line derivatives in the directions `(1, 0)` and `(0, 1)`):

* `wave_radial`: `□[a(s, |y|)] = a_ss − a_ρρ − (2/|y|) a_ρ` for `y ≠ 0` (Lemma 5);
* `integral_radial`: `∫_{ℝ³} G(|y|) dy = 4π ∫₀^∞ ρ² G(ρ) dρ` (Lemma 6);
* `integral_radial_boundary`: `∫₀^∞ ρ (a_ss − a_ρρ − (2/ρ) a_ρ)(ρ, ρ) dρ = a(0, 0)` for `a`
  smooth with compact support (Lemma 7).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology InnerProductSpace
open MeasureTheory Set Filter Function Metric

/-! ### Partial derivatives of a profile on `ℝ²` -/

/-! ### Lemma 5: `□` of a radial function -/

/-- The second derivative of `A(|y + s e|)` at `s = 0`, for a unit vector `e` and `y ≠ 0`. -/
theorem deriv_deriv_norm_line {A : ℝ → ℝ} (hA : ContDiff ℝ ∞ A) {y e : Space} (hy : y ≠ 0)
    (he : ‖e‖ = 1) :
    deriv (deriv fun s : ℝ => A ‖y + s • e‖) 0 =
      deriv (deriv A) ‖y‖ * (⟪y, e⟫_ℝ / ‖y‖) ^ 2 +
        deriv A ‖y‖ * (1 / ‖y‖ - ⟪y, e⟫_ℝ ^ 2 / ‖y‖ ^ 3) := by
  set ρ := ‖y‖ with hρdef
  set c := ⟪y, e⟫_ℝ with hcdef
  have hρ : 0 < ρ := norm_pos_iff.2 hy
  have hA1 : Differentiable ℝ A := hA.differentiable (by simp)
  have hA2 : Differentiable ℝ (deriv A) :=
    (contDiff_infty_iff_deriv.1 hA).2.differentiable (by simp)
  set P : ℝ → ℝ := fun s => ρ ^ 2 + 2 * c * s + s ^ 2 with hPdef
  have hnorm : ∀ s : ℝ, ‖y + s • e‖ = √(P s) := by
    intro s
    rw [← Real.sqrt_sq (norm_nonneg (y + s • e)), norm_add_sq_real, inner_smul_right, norm_smul,
      he, Real.norm_eq_abs, mul_one, sq_abs]
    congr 1
    simp only [hPdef]
    ring
  have hP : ∀ s, HasDerivAt P (2 * c + 2 * s) s := by
    intro s
    have h := (((hasDerivAt_id' s).const_mul (2 * c)).const_add (ρ ^ 2)).add (hasDerivAt_pow 2 s)
    exact h.congr_deriv (by norm_num)
  have hP0 : 0 < P 0 := by simp [hPdef, hρ]
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < P s :=
    (continuous_iff_continuousAt.1 (by simp only [hPdef]; fun_prop) 0).eventually
      (lt_mem_nhds hP0)
  have hr : ∀ s, 0 < P s → HasDerivAt (fun s => √(P s)) ((c + s) / √(P s)) s := by
    intro s hs
    have h := (hP s).sqrt (ne_of_gt hs)
    convert h using 1
    have : √(P s) ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    field_simp
  have hg : ∀ s, 0 < P s → HasDerivAt (fun s => A (√(P s)))
      (deriv A (√(P s)) * ((c + s) / √(P s))) s :=
    fun s hs => (hA1 _).hasDerivAt.comp s (hr s hs)
  have hfun : (fun s : ℝ => A ‖y + s • e‖) = fun s => A (√(P s)) := by
    funext s
    rw [hnorm]
  have hderiv : deriv (fun s : ℝ => A (√(P s))) =ᶠ[𝓝 0]
      fun s => deriv A (√(P s)) * ((c + s) / √(P s)) :=
    hpos.mono fun s hs => (hg s hs).deriv
  have hsq0 : √(P 0) = ρ := by
    simp only [hPdef]
    simp [Real.sqrt_sq hρ.le]
  have hs0 : √(P 0) ≠ 0 := by rw [hsq0]; exact hρ.ne'
  have h1 := (hA2 (√(P 0))).hasDerivAt.comp 0 (hr 0 hP0)
  have h2 := ((hasDerivAt_id' (0 : ℝ)).const_add c).div (hr 0 hP0) hs0
  have h3 : HasDerivAt (fun s => deriv A (√(P s)) * ((c + s) / √(P s))) _ 0 := h1.mul h2
  rw [hfun, hderiv.deriv_eq, h3.deriv]
  simp only [comp_apply, add_zero]
  rw [hsq0]
  field_simp

theorem sum_inner_single_sq (y : Space) :
    ∑ i : Fin 3, ⟪y, EuclideanSpace.single i (1 : ℝ)⟫_ℝ ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_single_right, Real.norm_eq_abs, sq_abs]
  simp

/-- G3, Lemma 5: `□[a(s, |y|)] = a_ss − a_ρρ − (2/|y|) a_ρ` at points with `y ≠ 0`. -/
theorem wave_radial {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (p : Point) (hp : p.2 ≠ 0) :
    wave (fun q : Point => a (q.1, ‖q.2‖)) p =
      partialS (partialS a) (p.1, ‖p.2‖) - partialR (partialR a) (p.1, ‖p.2‖) -
        2 / ‖p.2‖ * partialR a (p.1, ‖p.2‖) := by
  set A : ℝ → ℝ := fun ρ => a (p.1, ρ) with hAdef
  have hA : ContDiff ℝ ∞ A := ha.comp (contDiff_const.prodMk contDiff_id)
  -- the time part
  have ht : deriv (deriv fun s : ℝ => a ((p + s • timeDir).1, ‖(p + s • timeDir).2‖)) 0 =
      partialS (partialS a) (p.1, ‖p.2‖) := by
    have e : (fun s : ℝ => a ((p + s • timeDir).1, ‖(p + s • timeDir).2‖)) =
        fun s : ℝ => a ((p.1, ‖p.2‖) + s • ((1 : ℝ), (0 : ℝ))) := by
      funext s
      simp [timeDir]
    rw [e, ← lineDeriv_lineDeriv_eq]
    rfl
  -- the derivatives of `A`
  have hA' : ∀ ρ, deriv A ρ = partialR a (p.1, ρ) := by
    intro ρ
    have e : (fun u : ℝ => a ((p.1, ρ) + u • ((0 : ℝ), (1 : ℝ)))) = fun u => A (ρ + u) := by
      funext u
      simp [hAdef]
    change _ = deriv (fun u : ℝ => a ((p.1, ρ) + u • ((0 : ℝ), (1 : ℝ)))) 0
    rw [e, deriv_comp_const_add (f := A), add_zero]
  have hA'' : deriv (deriv A) ‖p.2‖ = partialR (partialR a) (p.1, ‖p.2‖) := by
    have e : (fun u : ℝ => a ((p.1, ‖p.2‖) + u • ((0 : ℝ), (1 : ℝ)))) =
        fun u => A (‖p.2‖ + u) := by
      funext u
      simp [hAdef]
    change _ = lineDeriv ℝ (fun z => lineDeriv ℝ a z (0, 1)) (p.1, ‖p.2‖) (0, 1)
    rw [lineDeriv_lineDeriv_eq, e]
    have e2 : (deriv fun u : ℝ => A (‖p.2‖ + u)) = fun u => deriv A (‖p.2‖ + u) :=
      funext fun u => deriv_comp_const_add (f := A) _ _
    rw [e2, deriv_comp_const_add (f := deriv A), add_zero]
  -- the space part
  have hs : ∀ i, deriv (deriv fun s : ℝ =>
      a ((p + s • spaceDir i).1, ‖(p + s • spaceDir i).2‖)) 0 =
      deriv (deriv A) ‖p.2‖ * (⟪p.2, EuclideanSpace.single i (1 : ℝ)⟫_ℝ / ‖p.2‖) ^ 2 +
        deriv A ‖p.2‖ * (1 / ‖p.2‖ - ⟪p.2, EuclideanSpace.single i (1 : ℝ)⟫_ℝ ^ 2 / ‖p.2‖ ^ 3) := by
    intro i
    have e : (fun s : ℝ => a ((p + s • spaceDir i).1, ‖(p + s • spaceDir i).2‖)) =
        fun s : ℝ => A ‖p.2 + s • EuclideanSpace.single i (1 : ℝ)‖ := by
      funext s
      simp [hAdef, spaceDir]
    rw [e]
    exact deriv_deriv_norm_line hA hp (by simp)
  have hρ : 0 < ‖p.2‖ := norm_pos_iff.2 hp
  have hsum := sum_inner_single_sq p.2
  rw [wave_apply_eq_deriv, ht, Finset.sum_congr rfl fun i _ => hs i, hA' ‖p.2‖, ← hA'']
  simp only [Fin.sum_univ_three] at hsum ⊢
  set α := deriv (deriv A) ‖p.2‖
  set β := partialR a (p.1, ‖p.2‖)
  set ρ := ‖p.2‖
  set c0 := ⟪p.2, EuclideanSpace.single 0 (1 : ℝ)⟫_ℝ
  set c1 := ⟪p.2, EuclideanSpace.single 1 (1 : ℝ)⟫_ℝ
  set c2 := ⟪p.2, EuclideanSpace.single 2 (1 : ℝ)⟫_ℝ
  have key : α * (c0 / ρ) ^ 2 + β * (1 / ρ - c0 ^ 2 / ρ ^ 3) +
      (α * (c1 / ρ) ^ 2 + β * (1 / ρ - c1 ^ 2 / ρ ^ 3)) +
      (α * (c2 / ρ) ^ 2 + β * (1 / ρ - c2 ^ 2 / ρ ^ 3)) = α + 2 / ρ * β := by
    calc _ = α * ((c0 ^ 2 + c1 ^ 2 + c2 ^ 2) / ρ ^ 2) +
          β * (3 / ρ - (c0 ^ 2 + c1 ^ 2 + c2 ^ 2) / ρ ^ 3) := by ring
      _ = α * (ρ ^ 2 / ρ ^ 2) + β * (3 / ρ - ρ ^ 2 / ρ ^ 3) := by rw [hsum]
      _ = α + 2 / ρ * β := by
        field_simp
        ring
  rw [key]
  ring

/-! ### Lemma 6: integrals of radial functions -/

/-- G3, Lemma 6: `∫_{ℝ³} G(|y|) dy = 4π ∫₀^∞ ρ² G(ρ) dρ`. -/
theorem integral_radial (G : ℝ → ℝ) :
    ∫ y : Space, G ‖y‖ = 4 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ ^ 2 * G ρ := by
  rw [integral_fun_norm_addHaar (μ := volume) G]
  have hvol : (volume : Measure Space).real (ball 0 1) = Real.pi * 4 / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    have : (0 : ℝ) ≤ Real.pi * 4 / 3 := by positivity
    simp [this]
  rw [hvol, finrank_euclideanSpace, Fintype.card_fin]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-! ### Lemma 7: the boundary term -/

/-- G3, Lemma 7: `∫₀^∞ ρ (a_ss − a_ρρ − (2/ρ) a_ρ)(ρ, ρ) dρ = a(0, 0)`. -/
theorem integral_radial_boundary {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) :
    ∫ ρ in Ioi (0 : ℝ), ρ * (partialS (partialS a) (ρ, ρ) - partialR (partialR a) (ρ, ρ) -
      2 / ρ * partialR a (ρ, ρ)) = a (0, 0) := by
  have hS := contDiff_partialS ha
  have hR := contDiff_partialR ha
  have hSS := contDiff_partialS hS
  have hRR := contDiff_partialR hR
  have c1 : ∀ {F : ℝ × ℝ → ℝ}, ContDiff ℝ ∞ F → ContDiff ℝ 1 F := fun h =>
    h.of_le (by exact_mod_cast le_top)
  set w : ℝ → ℝ := fun x => x * partialS a (x, x) - a (x, x) - x * partialR a (x, x) with hw
  set w' : ℝ → ℝ := fun x => x * (partialS (partialS a) (x, x) - partialR (partialR a) (x, x)) -
    2 * partialR a (x, x) with hw'
  have hderiv : ∀ x, HasDerivAt w (w' x) x := by
    intro x
    have h1 := ((hasDerivAt_id x).mul (hasDerivAt_diag (c1 hS) x)).sub (hasDerivAt_diag (c1 ha) x)
    have h2 : HasDerivAt w _ x := h1.sub ((hasDerivAt_id x).mul (hasDerivAt_diag (c1 hR) x))
    convert h2 using 1
    rw [partialR_partialS ha]
    simp only [id, hw']
    ring
  have hcw' : Continuous w' := by
    simp only [hw']
    have := hSS.continuous
    have := hRR.continuous
    have := hR.continuous
    fun_prop
  have hsupp : ∀ {F : ℝ × ℝ → ℝ} (v : ℝ × ℝ) (x : ℝ), (x, x) ∉ tsupport F →
      lineDeriv ℝ F (x, x) v = 0 := fun {F} v x hx =>
    image_eq_zero_of_notMem_tsupport (f := fun z => lineDeriv ℝ F z v)
      fun h => hx (tsupport_lineDeriv_subset F v h)
  have hzero' : ∀ x, (x, x) ∉ tsupport a → w x = 0 ∧ w' x = 0 := by
    intro x hx
    have hRx : (x, x) ∉ tsupport (partialR a) := fun h => hx (tsupport_lineDeriv_subset _ _ h)
    have hSx : (x, x) ∉ tsupport (partialS a) := fun h => hx (tsupport_lineDeriv_subset _ _ h)
    have e1 : partialS a (x, x) = 0 := hsupp _ x hx
    have e2 : partialR a (x, x) = 0 := hsupp _ x hx
    have e3 : partialS (partialS a) (x, x) = 0 := hsupp _ x hSx
    have e4 : partialR (partialR a) (x, x) = 0 := hsupp _ x hRx
    have e5 : a (x, x) = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hw, hw', e1, e2, e3, e4, e5]
  have hint : IntegrableOn w' (Ioi 0) := by
    obtain ⟨R, hR⟩ := hca.isCompact.isBounded.subset_closedBall 0
    refine (hcw'.integrable_of_hasCompactSupport ?_).integrableOn
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun x hx => ?_
    refine (hzero' x fun hmem => hx ?_).2
    have h := hR hmem
    rw [mem_closedBall_zero_iff] at h ⊢
    simpa [Prod.norm_def] using h
  have hlim : ∀ᶠ x in atTop, w x = 0 :=
    (eventually_diag_eq_zero hca).mono fun x hx => (hzero' x hx).1
  have key := integral_Ioi_deriv_eq_neg (w := w) (w' := w')
    (hderiv 0).continuousAt.continuousWithinAt (fun x _ => hderiv x) hint hlim
  have hcongr : ∫ ρ in Ioi (0 : ℝ), ρ * (partialS (partialS a) (ρ, ρ) -
      partialR (partialR a) (ρ, ρ) - 2 / ρ * partialR a (ρ, ρ)) = ∫ x in Ioi (0 : ℝ), w' x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    have : ρ ≠ 0 := (ne_of_gt hρ)
    simp only [hw']
    field_simp
  rw [hcongr, key]
  simp [hw]

end LinearAQFT.Minkowski
