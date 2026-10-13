/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Mass
import LinearAQFT.Analysis.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Huygens' principle

Stage H, milestone H4, Section 2 (Definition 5, Proposition 6, Lemma 7, Proposition 8, Lemmas 9
and 10, Theorems 11 and 12). For `μ = 0` the Green operators propagate only along the light cone:
`supp G^± f ⊆ supp f ± ∂C⁺` (the strong Huygens principle). For every `μ ≠ 0` there are a test
function `f` and a point `p` in the open future cone of every point of `supp f` with
`G_μ⁺ f(p) ≠ 0`. Hence Huygens' principle holds exactly when `μ = 0`.

The proof of the failure uses only the first two terms of the series: `G⁺ f(p) = 0` by the massless
case, `(G⁺)² f(p) > 0` by positivity, and the tail bound makes `G_ν⁺ f(p) ≠ 0` for small `ν ≠ 0`;
dilation carries this to every `μ ≠ 0`.

## Main results

* `coneSurface`, `chronLT` (Definition 5).
* `supp_gret_subset_coneSurface`, `supp_gadv_subset_coneSurface`,
  `gret_apply_eq_zero_of_chronLT`, `gadv_apply_eq_zero_of_chronLT` (Proposition 6).
* `kirchhoff_pos` (Lemma 7); `kpow_two_pos` (Proposition 8).
* `abs_gmu_sub_le` (Lemma 9); `kirchhoff_comp_smul`, `kpow_comp_smul`, `gmu_comp_smul` (Lemma 10).
* `exists_gretMu_ne_zero`, `exists_gadvMu_ne_zero` (Theorem 11).
* `huygens_iff`, `huygens_iff_past` (Theorem 12).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology Pointwise
open MeasureTheory Set Filter Function Metric

/-! ### Definition 5 -/

/-- H4, Definition 5: the future light-cone surface `∂C⁺ = {v : v⁰ = |v⃗|}`. -/
def coneSurface : Set Point := {v | v.1 = ‖v.2‖}

/-- H4, Definition 5: chronological precedence `p ≪ q`, i.e. `q − p` lies in the open future
cone. -/
def chronLT (p q : Point) : Prop := ‖q.2 - p.2‖ < q.1 - p.1

theorem isClosed_coneSurface : IsClosed coneSurface :=
  isClosed_eq continuous_fst continuous_snd.norm

/-! ### Proposition 6: the strong Huygens principle -/

/-- `G⁺ f` vanishes off `supp f + ∂C⁺`. -/
theorem support_kirchhoff_subset {f : Point → ℝ} (hf : Continuous f) :
    Function.support (kirchhoff coneMeasure f) ⊆ tsupport f + coneSurface := by
  intro p hp
  by_contra hn
  apply hp
  have h0 : ∀ y : Space, f (p.1 - ‖y‖, p.2 - y) = 0 := fun y => by
    by_contra hne
    exact hn ⟨(p.1 - ‖y‖, p.2 - y), subset_tsupport _ hne, (‖y‖, y), rfl,
      Prod.ext (by simp) (by simp)⟩
  rw [kirchhoff_coneMeasure_apply hf]
  simp [h0]

/-- `G⁻ f` vanishes off `supp f − ∂C⁺`. -/
theorem support_kirchhoffPast_subset {f : Point → ℝ} (hf : Continuous f) :
    Function.support (kirchhoff coneMeasurePast f) ⊆ tsupport f + -coneSurface := by
  intro p hp
  by_contra hn
  apply hp
  have h0 : ∀ y : Space, f (p.1 + ‖y‖, p.2 - y) = 0 := fun y => by
    by_contra hne
    refine hn ⟨(p.1 + ‖y‖, p.2 - y), subset_tsupport _ hne, (-‖y‖, y), ?_,
      Prod.ext (by simp) (by simp)⟩
    change (-(-‖y‖, y) : Point).1 = ‖(-(-‖y‖, y) : Point).2‖
    simp
  rw [kirchhoff_coneMeasurePast_apply hf]
  simp [h0]

/-- H4, Proposition 6 (strong Huygens principle, `μ = 0`): `supp G⁺ f ⊆ supp f + ∂C⁺`. -/
theorem supp_gret_subset_coneSurface (f : TestFun) :
    supp (gret f) ⊆ supp (incl f) + coneSurface :=
  closure_minimal (support_kirchhoff_subset f.continuous)
    (isClosed_coneSurface.add_left_of_isCompact f.hasCompactSupport)

/-- H4, Proposition 6: `supp G⁻ f ⊆ supp f − ∂C⁺`. -/
theorem supp_gadv_subset_coneSurface (f : TestFun) :
    supp (gadv f) ⊆ supp (incl f) + -coneSurface :=
  closure_minimal (support_kirchhoffPast_subset f.continuous)
    (isClosed_coneSurface.neg.add_left_of_isCompact f.hasCompactSupport)

/-- H4, Proposition 6: `G⁺ f (p) = 0` when `p` lies in the open future cone of every point of
`supp f`. -/
theorem gret_apply_eq_zero_of_chronLT (f : TestFun) {p : Point}
    (hp : ∀ q ∈ supp (incl f), chronLT q p) : (gret f : Point → ℝ) p = 0 := by
  by_contra hne
  obtain ⟨q, hq, v, hv, rfl⟩ := supp_gret_subset_coneSurface f (subset_tsupport _ hne)
  have h := hp q hq
  simp only [chronLT, Prod.fst_add, Prod.snd_add, add_sub_cancel_left] at h
  exact (lt_irrefl _) (hv ▸ h)

/-- H4, Proposition 6: `G⁻ f (p) = 0` when `p` lies in the open past cone of every point of
`supp f`. -/
theorem gadv_apply_eq_zero_of_chronLT (f : TestFun) {p : Point}
    (hp : ∀ q ∈ supp (incl f), chronLT p q) : (gadv f : Point → ℝ) p = 0 := by
  by_contra hne
  obtain ⟨q, hq, v, hv, rfl⟩ := supp_gadv_subset_coneSurface f (subset_tsupport _ hne)
  have h := hp q hq
  have hv' : -v.1 = ‖v.2‖ := by simpa [coneSurface] using hv
  simp only [chronLT, Prod.fst_add, Prod.snd_add, sub_add_cancel_left, norm_neg] at h
  linarith

/-! ### Lemma 7 and Proposition 8: positivity -/

/-- H4, Lemma 7: for continuous `h ≥ 0` with integrable Kirchhoff integrand at `p`, if
`h (p⁰ − |y₁|, p⃗ − y₁) > 0` for some `y₁ ≠ 0`, then `G⁺ h (p) > 0`. -/
theorem kirchhoff_pos {h : Point → ℝ} (hh : Continuous h) (h0 : ∀ q, 0 ≤ h q) {p : Point}
    (hi : Integrable fun y : Space => h (p.1 - ‖y‖, p.2 - y) / ‖y‖) {y₁ : Space} (hy : y₁ ≠ 0)
    (hpos : 0 < h (p.1 - ‖y₁‖, p.2 - y₁)) : 0 < kirchhoff coneMeasure h p := by
  set g : Space → ℝ := fun y => h (p.1 - ‖y‖, p.2 - y) / ‖y‖ with hg
  have hg0 : 0 ≤ g := fun y => div_nonneg (h0 _) (norm_nonneg _)
  have hgc : ContinuousAt g y₁ := by
    refine ContinuousAt.div ?_ continuous_norm.continuousAt (norm_ne_zero_iff.2 hy)
    exact (hh.comp (by fun_prop)).continuousAt
  have hgy : 0 < g y₁ := div_pos hpos (norm_pos_iff.2 hy)
  have hev : {y | 0 < g y} ∈ 𝓝 y₁ := hgc.eventually (lt_mem_nhds hgy)
  have hmeas : 0 < volume (Function.support g) :=
    (Measure.measure_pos_of_mem_nhds volume hev).trans_le (measure_mono fun y hy => (ne_of_gt hy))
  rw [kirchhoff_coneMeasure_apply hh]
  exact mul_pos (by positivity) ((integral_pos_iff_support_of_nonneg hg0 hi).2 hmeas)

/-- H4, Proposition 8: for a test function `f ≥ 0` with `f (x₀) > 0` and `x₀ ≪ p`,
`(G⁺)² f (p) > 0`. -/
theorem kpow_two_pos {f : TestFun} (hf0 : ∀ q, 0 ≤ f q) {x₀ p : Point} (hx : 0 < f x₀)
    (hp : chronLT x₀ p) : 0 < kpow coneMeasure 2 f p := by
  set τ := p.1 - x₀.1 with hτ
  set d := p.2 - x₀.2 with hd
  have hdτ : ‖d‖ < τ := hp
  obtain ⟨u, hu, hdu⟩ := exists_unit_smul d
  set y₁ : Space := ((τ + ‖d‖) / 2) • u with hy₁
  have hny₁ : ‖y₁‖ = (τ + ‖d‖) / 2 := by
    rw [hy₁, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith [norm_nonneg d])]
  have hy₁0 : y₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hny₁
    linarith [norm_nonneg d]
  set q : Point := (p.1 - ‖y₁‖, p.2 - y₁) with hq
  set z₁ : Space := q.2 - x₀.2 with hz₁
  have hz₁e : z₁ = ((‖d‖ - τ) / 2) • u := by
    rw [hz₁, hq]
    change p.2 - y₁ - x₀.2 = _
    rw [show p.2 - y₁ - x₀.2 = d - y₁ by rw [hd]; abel, hy₁]
    nth_rewrite 1 [hdu]
    rw [← sub_smul]
    congr 1
    ring
  have hnz₁ : ‖z₁‖ = (τ - ‖d‖) / 2 := by
    rw [hz₁e, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hz₁0 : z₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnz₁
    linarith
  have hx₀ : ((q.1 - ‖z₁‖, q.2 - z₁) : Point) = x₀ := by
    refine Prod.ext ?_ ?_
    · change p.1 - ‖y₁‖ - ‖z₁‖ = x₀.1
      rw [hny₁, hnz₁]
      linarith
    · change q.2 - (q.2 - x₀.2) = x₀.2
      abel
  have h1 : 0 < kirchhoff coneMeasure f q :=
    kirchhoff_pos f.continuous hf0
      (integrable_kirchhoff_integrand_of_futureSupported f.continuous
        (futureSupported_testFun f) q) hz₁0 (by rw [hx₀]; exact hx)
  obtain ⟨K, hK, hKs⟩ := futureSupported_testFun f
  have hGc : Continuous (kirchhoff coneMeasure f) := (contDiff_kpow f.contDiff hK hKs 1).continuous
  exact kirchhoff_pos hGc (kirchhoff_nonneg coneMeasure hf0)
    (integrable_kirchhoff_integrand_of_futureSupported hGc
      ⟨K, hK, tsupport_kpow_subset f.contDiff hK hKs 1⟩ p) hy₁0 h1

/-! ### Lemma 9: the tail bound -/

/-- H4, Lemma 9: for a test function `f` vanishing before `t₀` with `|f| ≤ C`, and
`τ = p⁰ − t₀ ≥ 0`,
`|G_μ⁺ f (p) − G⁺ f (p) + μ (G⁺)² f (p)| ≤ C μ² τ⁶ cosh(√|μ| τ)`. -/
theorem abs_gmu_sub_le (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    {t₀ C : ℝ} (h0 : ∀ q : Point, q.1 < t₀ → f q = 0) (hC : ∀ q : Point, |f q| ≤ C)
    {p : Point} (hp0 : t₀ ≤ p.1) :
    |gmu μ f p - kirchhoff coneMeasure f p + μ * kpow coneMeasure 2 f p| ≤
      C * μ ^ 2 * (p.1 - t₀) ^ 6 * Real.cosh (Real.sqrt |μ| * (p.1 - t₀)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set a : ℕ → ℝ := fun k => (-μ) ^ k * kpow coneMeasure (k + 1) f p with ha
  have hs : Summable a := summable_gmu μ hf hcf p
  have hs1 : Summable fun k => a (k + 1) := (summable_nat_add_iff 1).2 hs
  have hsplit : gmu μ f p = a 0 + (a 1 + ∑' k, a (k + 2)) := by
    change ∑' k, a k = _
    rw [hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
  have ha0 : a 0 = kirchhoff coneMeasure f p := by simp [ha, kpow_succ]
  have ha1 : a 1 = -μ * kpow coneMeasure 2 f p := by simp [ha]
  set τ := p.1 - t₀ with hτ
  set x := Real.sqrt |μ| * τ with hx
  have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
  have hxμ : x ^ 4 = μ ^ 2 * τ ^ 4 := by
    rw [hx, mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (abs_nonneg μ), sq_abs]
  have hbound : ∀ k, ‖a (k + 2)‖ ≤ C * μ ^ 2 * τ ^ 6 * (x ^ (2 * k) / (2 * k).factorial) := by
    intro k
    have h := abs_gmu_term_le μ hf hcf hC0 h0 hC (k + 2) hp0
    rw [Real.norm_eq_abs]
    refine h.trans ?_
    have hfac : ((2 * k).factorial : ℝ) ≤ (2 * (k + 2)).factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hx4 : x ^ (2 * (k + 2)) = x ^ 4 * x ^ (2 * k) := by ring
    have hxx : 0 ≤ x ^ 4 * x ^ (2 * k) := mul_nonneg (by positivity) (by rw [pow_mul]; positivity)
    rw [hx4]
    calc C * τ ^ 2 * (x ^ 4 * x ^ (2 * k) / (2 * (k + 2)).factorial)
        ≤ C * τ ^ 2 * (x ^ 4 * x ^ (2 * k) / (2 * k).factorial) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hxx (by positivity) hfac)
            (by positivity)
      _ = C * μ ^ 2 * τ ^ 6 * (x ^ (2 * k) / (2 * k).factorial) := by rw [hxμ]; ring
  have hsum := (Real.hasSum_cosh x).mul_left (C * μ ^ 2 * τ ^ 6)
  have key := tsum_of_norm_bounded hsum hbound
  rw [Real.norm_eq_abs] at key
  rw [hsplit, ha0, ha1]
  convert key using 2
  ring

/-! ### Lemma 10: dilation -/

/-- H4, Lemma 10(a): `G⁺ f_λ (λ p) = λ² G⁺ f (p)` for continuous `f`, `f_λ(q) = f(q/λ)`. -/
theorem kirchhoff_comp_smul {f : Point → ℝ} (hf : Continuous f) {l : ℝ} (hl : 0 < l) (p : Point) :
    kirchhoff coneMeasure (fun q => f (l⁻¹ • q)) (l • p) = l ^ 2 * kirchhoff coneMeasure f p := by
  have hfl : Continuous fun q : Point => f (l⁻¹ • q) := hf.comp (continuous_const_smul _)
  rw [kirchhoff_coneMeasure_apply hfl, kirchhoff_coneMeasure_apply hf]
  set g : Space → ℝ := fun y => f (l⁻¹ • ((l • p).1 - ‖y‖, (l • p).2 - y)) / ‖y‖ with hg
  have hcomp := Measure.integral_comp_smul (μ := (volume : Measure Space)) g l
  rw [finrank_euclideanSpace_fin] at hcomp
  have hgl : ∀ z : Space, g (l • z) = l⁻¹ * (f (p.1 - ‖z‖, p.2 - z) / ‖z‖) := by
    intro z
    have hpt : (l⁻¹ • ((l • p).1 - ‖l • z‖, (l • p).2 - l • z) : Point) = (p.1 - ‖z‖, p.2 - z) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_smul, Real.norm_eq_abs,
          abs_of_pos hl]
        field_simp
      · simp only [Prod.smul_fst, Prod.smul_snd, ← smul_sub, smul_smul,
          inv_mul_cancel₀ hl.ne', one_smul]
    simp only [hg]
    rw [hpt, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
    field_simp
  simp_rw [hgl, integral_const_mul] at hcomp
  rw [abs_of_pos (by positivity : (0 : ℝ) < (l ^ 3)⁻¹), smul_eq_mul] at hcomp
  have hG : integral volume g = l ^ 2 * ∫ y : Space, f (p.1 - ‖y‖, p.2 - y) / ‖y‖ := by
    calc integral volume g = l ^ 3 * ((l ^ 3)⁻¹ * ∫ x, g x) := by field_simp
      _ = l ^ 3 * (l⁻¹ * ∫ y : Space, f (p.1 - ‖y‖, p.2 - y) / ‖y‖) := by rw [hcomp]
      _ = l ^ 2 * ∫ y : Space, f (p.1 - ‖y‖, p.2 - y) / ‖y‖ := by field_simp
  rw [hG]
  ring

/-- H4, Lemma 10(b): `(G⁺)^k f_λ = λ^{2k} ((G⁺)^k f)_λ` for a test function `f`. -/
theorem kpow_comp_smul {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) {l : ℝ}
    (hl : 0 < l) (k : ℕ) :
    kpow coneMeasure k (fun q => f (l⁻¹ • q)) =
      fun q => l ^ (2 * k) * kpow coneMeasure k f (l⁻¹ • q) := by
  obtain ⟨K, hK, hKs⟩ := futureSupported_of_hasCompactSupport hcf
  induction k with
  | zero => funext q; simp
  | succ k ih =>
    have hc : Continuous (kpow coneMeasure k f) := (contDiff_kpow hf hK hKs k).continuous
    funext q
    rw [kpow_succ, kpow_succ, ih]
    have hsm : (fun q => l ^ (2 * k) * kpow coneMeasure k f (l⁻¹ • q)) =
        l ^ (2 * k) • fun q => kpow coneMeasure k f (l⁻¹ • q) := rfl
    rw [hsm, kirchhoff_smul coneMeasure, Pi.smul_apply, smul_eq_mul]
    have h := kirchhoff_comp_smul hc hl (l⁻¹ • q)
    rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul] at h
    rw [h]
    ring

/-- H4, Lemma 10(b): `G_μ⁺ f_λ (λ p) = λ² G_{λ²μ}⁺ f (p)` for a test function `f`. -/
theorem gmu_comp_smul (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    {l : ℝ} (hl : 0 < l) (p : Point) :
    gmu μ (fun q => f (l⁻¹ • q)) (l • p) = l ^ 2 * gmu (l ^ 2 * μ) f p := by
  simp only [gmu, kpow_comp_smul hf hcf hl, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  rw [← tsum_mul_left]
  congr 1
  funext k
  rw [neg_mul_eq_mul_neg, mul_pow, ← pow_mul]
  ring

/-! ### Theorems 11 and 12: Huygens' principle holds exactly at `μ = 0` -/

/-- Chronological precedence is invariant under dilations `λ > 0`. -/
theorem chronLT_smul {l : ℝ} (hl : 0 < l) {p q : Point} :
    chronLT (l • p) (l • q) ↔ chronLT p q := by
  simp only [chronLT, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos hl, ← mul_sub]
  exact mul_lt_mul_iff_of_pos_left hl

/-- Time reflection reverses chronological precedence. -/
theorem chronLT_timeRefl {p q : Point} : chronLT (timeRefl p) (timeRefl q) ↔ chronLT q p := by
  simp only [chronLT, timeRefl]
  rw [norm_sub_rev]
  constructor <;> intro h <;> linarith

/-- The dilated test function `f_λ(q) = f(q/λ)`. -/
noncomputable def dilateTest {l : ℝ} (hl : l ≠ 0) (f : TestFun) : TestFun :=
  ⟨fun q => f (l⁻¹ • q), f.contDiff.comp (contDiff_const_smul _),
    f.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero l⁻¹ (inv_ne_zero hl)),
    by simp⟩

@[simp] theorem dilateTest_apply {l : ℝ} (hl : l ≠ 0) (f : TestFun) (q : Point) :
    dilateTest hl f q = f (l⁻¹ • q) := rfl

/-- The time-reflected test function `f ∘ R`. -/
noncomputable def timeReflTest (f : TestFun) : TestFun :=
  ⟨f ∘ timeRefl, f.contDiff.comp contDiff_timeRefl,
    f.hasCompactSupport.comp_homeomorph timeReflHomeo,
    by simp⟩

@[simp] theorem timeReflTest_apply (f : TestFun) (q : Point) :
    timeReflTest f q = f (timeRefl q) := rfl

/-- The bump used in Theorem 11: `0 ≤ b ≤ 1`, `b(0) = 1`, `supp b` the closed ball of radius
`1/4` about `0` (in the product norm `max(|t|, |x⃗|)`). -/
noncomputable def huygensBump : ContDiffBump (0 : Point) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

theorem huygensBump_rIn : huygensBump.rIn = 1 / 8 := rfl

theorem huygensBump_rOut : huygensBump.rOut = 1 / 4 := rfl

/-- The bump as a test function. -/
noncomputable def huygensTest : TestFun :=
  ⟨huygensBump, huygensBump.contDiff, huygensBump.hasCompactSupport, by simp⟩

/-- The point `p₀ = (1, 0⃗)`. -/
def huygensPoint : Point := (1, 0)

theorem chronLT_huygensPoint {q : Point} (hq : q ∈ tsupport (huygensBump : Point → ℝ)) :
    chronLT q huygensPoint := by
  rw [huygensBump.tsupport_eq, mem_closedBall_zero_iff, huygensBump_rOut] at hq
  have h1 : q.1 ≤ 1 / 4 :=
    (le_abs_self _).trans ((Real.norm_eq_abs q.1).symm ▸ (norm_fst_le q).trans hq)
  have h2 : ‖q.2‖ ≤ 1 / 4 := (norm_snd_le q).trans hq
  change ‖(0 : Space) - q.2‖ < 1 - q.1
  rw [zero_sub, norm_neg]
  linarith

theorem huygensBump_eq_zero {q : Point} (hq : q.1 < -(1 / 4)) : huygensBump q = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hs => ?_
  rw [huygensBump.tsupport_eq, mem_closedBall_zero_iff, huygensBump_rOut] at hs
  have h := (norm_fst_le q).trans hs
  rw [Real.norm_eq_abs] at h
  linarith [neg_abs_le q.1]

/-- For small `ν ≠ 0`, `G_ν⁺ b (p₀) ≠ 0`. -/
theorem exists_small_gmu_ne_zero :
    ∃ δ > 0, ∀ ν : ℝ, ν ≠ 0 → |ν| < δ → gmu ν huygensBump huygensPoint ≠ 0 := by
  have hb : ContDiff ℝ ∞ (huygensBump : Point → ℝ) := huygensBump.contDiff
  have hbc := huygensBump.hasCompactSupport
  have hG0 : kirchhoff coneMeasure huygensBump huygensPoint = 0 :=
    gret_apply_eq_zero_of_chronLT huygensTest fun q hq => chronLT_huygensPoint hq
  set A := kpow coneMeasure 2 huygensBump huygensPoint with hA
  have hApos : 0 < A :=
    kpow_two_pos (f := huygensTest) (fun q => huygensBump.nonneg) (x₀ := 0)
      (by
        change 0 < huygensBump 0
        have h0 : (0 : Point) ∈ closedBall 0 huygensBump.rIn :=
          mem_closedBall_self (by rw [huygensBump_rIn]; norm_num)
        rw [huygensBump.one_of_mem_closedBall h0]
        exact one_pos)
      (by change ‖(0 : Space) - 0‖ < 1 - 0; norm_num)
  set τ : ℝ := 5 / 4 with hτ
  set B : ℝ := τ ^ 6 * Real.cosh τ with hB
  have hBpos : 0 < B := by positivity
  refine ⟨min 1 (A / B), lt_min one_pos (div_pos hApos hBpos), fun ν hν hνδ => ?_⟩
  have hν1 : |ν| ≤ 1 := (hνδ.trans_le (min_le_left _ _)).le
  have hνA : |ν| * B < A := by
    have := hνδ.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hBpos] at this
  have htail := abs_gmu_sub_le ν hb hbc (fun q hq => huygensBump_eq_zero hq)
    (fun q => by rw [abs_of_nonneg huygensBump.nonneg]; exact huygensBump.le_one)
    (p := huygensPoint) (by norm_num [huygensPoint])
  have hτp : huygensPoint.1 - -(1 / 4) = τ := by norm_num [huygensPoint, hτ]
  rw [hτp, hG0, sub_zero, one_mul] at htail
  have hcosh : Real.cosh (Real.sqrt |ν| * τ) ≤ Real.cosh τ := by
    rw [Real.cosh_le_cosh, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.sqrt_le_one.mpr hν1)
  intro h0
  rw [h0, zero_add, abs_mul] at htail
  have hν0 : 0 < |ν| := abs_pos.2 hν
  have : |ν| * A ≤ |ν| * (|ν| * B) := by
    calc |ν| * A = |ν| * |A| := by rw [abs_of_pos hApos]
      _ ≤ ν ^ 2 * τ ^ 6 * Real.cosh (Real.sqrt |ν| * τ) := htail
      _ ≤ ν ^ 2 * τ ^ 6 * Real.cosh τ := by gcongr
      _ = |ν| * (|ν| * B) := by rw [hB, ← sq_abs]; ring
  have := le_of_mul_le_mul_left this hν0
  linarith

/-- H4, Theorem 11: for every `μ ≠ 0` there are a test function `f` and a point `p` in the open
future cone of every point of `supp f` with `G_μ⁺ f (p) ≠ 0`. -/
theorem exists_gretMu_ne_zero {μ : ℝ} (hμ : μ ≠ 0) :
    ∃ (f : TestFun) (p : Point), (∀ q ∈ supp (incl f), chronLT q p) ∧
      (gretMu μ f : Point → ℝ) p ≠ 0 := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_gmu_ne_zero
  have hμ0 : 0 < |μ| := abs_pos.2 hμ
  set l := Real.sqrt (δ / 2 / |μ|) with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 (by positivity)
  have hl2 : l ^ 2 = δ / 2 / |μ| := Real.sq_sqrt (by positivity)
  have hν : |l ^ 2 * μ| = δ / 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < l ^ 2), hl2]
    field_simp
  refine ⟨dilateTest hl0.ne' huygensTest, l • huygensPoint, fun q hq => ?_, ?_⟩
  · have hq' := tsupport_comp_subset_preimage (huygensBump : Point → ℝ)
      (continuous_const_smul l⁻¹) hq
    have h := chronLT_huygensPoint hq'
    rwa [← chronLT_smul hl0, smul_smul, mul_inv_cancel₀ hl0.ne', one_smul] at h
  · change gmu μ (fun q => huygensBump (l⁻¹ • q)) (l • huygensPoint) ≠ 0
    rw [gmu_comp_smul μ (huygensBump.contDiff : ContDiff ℝ ∞ (huygensBump : Point → ℝ))
      huygensBump.hasCompactSupport hl0]
    refine mul_ne_zero (pow_ne_zero _ hl0.ne') (hsmall _ ?_ ?_)
    · exact mul_ne_zero (pow_ne_zero _ hl0.ne') hμ
    · rw [hν]; linarith

/-- H4, Theorem 11: for every `μ ≠ 0` there are a test function `f` and a point `p` in the open
past cone of every point of `supp f` with `G_μ⁻ f (p) ≠ 0`. -/
theorem exists_gadvMu_ne_zero {μ : ℝ} (hμ : μ ≠ 0) :
    ∃ (f : TestFun) (p : Point), (∀ q ∈ supp (incl f), chronLT p q) ∧
      (gadvMu μ f : Point → ℝ) p ≠ 0 := by
  obtain ⟨f, p, hp, hne⟩ := exists_gretMu_ne_zero hμ
  refine ⟨timeReflTest f, timeRefl p, fun q hq => ?_, ?_⟩
  · have hq' := tsupport_comp_subset_preimage (f : Point → ℝ) continuous_timeRefl hq
    have h := hp _ hq'
    rwa [← chronLT_timeRefl, timeRefl_timeRefl] at h
  · have hR : ContDiff ℝ ∞ (f ∘ timeRefl) := f.contDiff.comp contDiff_timeRefl
    have hcR : HasCompactSupport (f ∘ timeRefl) := f.hasCompactSupport.comp_homeomorph timeReflHomeo
    change gmuPast μ (f ∘ timeRefl) (timeRefl p) ≠ 0
    rw [gmuPast_eq μ hR hcR]
    have hff : (f ∘ timeRefl) ∘ timeRefl = (f : Point → ℝ) := by
      funext q
      simp
    simpa [hff] using hne

/-- H4, Theorem 12: Huygens' principle holds for `G_μ⁺` exactly when `μ = 0`. -/
theorem huygens_iff (μ : ℝ) :
    (∀ (f : TestFun) (p : Point), (∀ q ∈ supp (incl f), chronLT q p) →
      (gretMu μ f : Point → ℝ) p = 0) ↔ μ = 0 := by
  constructor
  · intro h
    by_contra hμ
    obtain ⟨f, p, hp, hne⟩ := exists_gretMu_ne_zero hμ
    exact hne (h f p hp)
  · rintro rfl f p hp
    rw [gretMu_zero]
    exact gret_apply_eq_zero_of_chronLT f hp

/-- H4, Theorem 12: Huygens' principle holds for `G_μ⁻` exactly when `μ = 0`. -/
theorem huygens_iff_past (μ : ℝ) :
    (∀ (f : TestFun) (p : Point), (∀ q ∈ supp (incl f), chronLT p q) →
      (gadvMu μ f : Point → ℝ) p = 0) ↔ μ = 0 := by
  constructor
  · intro h
    by_contra hμ
    obtain ⟨f, p, hp, hne⟩ := exists_gadvMu_ne_zero hμ
    exact hne (h f p hp)
  · rintro rfl f p hp
    rw [gadvMu_zero]
    exact gadv_apply_eq_zero_of_chronLT f hp

end LinearAQFT.Minkowski
