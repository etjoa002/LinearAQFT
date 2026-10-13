/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Extension
import LinearAQFT.Minkowski.Lorentz
import LinearAQFT.Analysis.Sums
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Green operators of the Klein–Gordon operator as a series

Stage H, milestone H3 (Definition 1, Lemma 2, Propositions 3, 4, Theorem 5, Propositions 6–8,
Corollary 9). For `μ ∈ ℝ` and a test function `f`,
`G_μ^± f = Σ_k (−μ)^k (G^±)^{k+1} f` converges absolutely, uniformly on every set `{q⁰ ≤ T}`, by
the power bound of milestone H2; it is smooth, with derivative `Σ_i G_μ^± (∂_{e_i} f) e^i`;
`(□ + μ) G_μ^± f = f` and `G_μ^± (□ + μ) f = f` by telescoping; its support lies in `J^±(supp f)`;
`⟨f, G_μ⁺ g⟩ = ⟨g, G_μ⁻ f⟩`; and `G_0^± = G^±`.

## Main results

* `gmu`, `gmuPast` (Definition 1).
* `kirchhoff_add_of_futureSupported`, `kpow_add`, `kpow_smul`, `kpow_succ'` (Lemma 2).
* `summable_gmu`, `abs_gmu_term_le`, `gmu_add`, `gmu_smul` (Proposition 3).
* `hasFDerivAt_gmu`, `dirDeriv_gmu`, `contDiff_gmu` (Proposition 4).
* `wave_gmu`, `gmu_kg` (Theorem 5); `tsupport_gmu_subset` (Proposition 6).
* `gmuPast_eq` and the advanced statements (Proposition 7); `integral_mul_gmu` (Proposition 8).
* `gmu_zero`, `gmuPast_zero` (Corollary 9).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology
open MeasureTheory Set Filter Function Metric

/-! ### Definition 1 -/

/-- H3, Definition 1: `G_μ⁺ f = Σ_k (−μ)^k (G⁺)^{k+1} f`, pointwise. -/
noncomputable def gmu (μ : ℝ) (f : Point → ℝ) (p : Point) : ℝ :=
  ∑' k : ℕ, (-μ) ^ k * kpow coneMeasure (k + 1) f p

/-- H3, Definition 1: `G_μ⁻ f = Σ_k (−μ)^k (G⁻)^{k+1} f`, pointwise. -/
noncomputable def gmuPast (μ : ℝ) (f : Point → ℝ) (p : Point) : ℝ :=
  ∑' k : ℕ, (-μ) ^ k * kpow coneMeasurePast (k + 1) f p

/-! ### Lemma 2: linearity on future-supported functions -/

/-- A compact set has a lowest time. -/
theorem exists_time_lower_bound {K : Set Point} (hK : IsCompact K) :
    ∃ t : ℝ, ∀ k ∈ K, t ≤ k.1 := by
  obtain ⟨t, ht⟩ := hK.bddBelow_image continuous_fst.continuousOn
  exact ⟨t, fun k hk => ht ⟨k, hk, rfl⟩⟩

/-- H3, Lemma 2: the Kirchhoff integrand of a continuous future-supported function is
integrable. -/
theorem integrable_kirchhoff_integrand_of_futureSupported {h : Point → ℝ} (hh : Continuous h)
    (hs : FutureSupported h) (p : Point) :
    Integrable (fun y : Space => h (p.1 - ‖y‖, p.2 - y) / ‖y‖) := by
  obtain ⟨K, hK, hKs⟩ := hs
  obtain ⟨t, ht⟩ := exists_time_lower_bound hK
  refine integrable_div_norm (hh.comp (by fun_prop)) ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (p.1 - t)) fun y hy => ?_
  by_contra hne
  obtain ⟨k, hk, hkq⟩ := hKs (subset_tsupport _ hne)
  apply hy
  rw [mem_closedBall, dist_zero_right]
  have h1 := ht k hk
  have h2 : ‖(p.2 - y) - k.2‖ ≤ (p.1 - ‖y‖) - k.1 := hkq
  have h3 := norm_nonneg ((p.2 - y) - k.2)
  linarith

/-- H3, Lemma 2: `G⁺` is additive on continuous future-supported functions. -/
theorem kirchhoff_add_of_futureSupported {u w : Point → ℝ} (hu : Continuous u)
    (hw : Continuous w) (hus : FutureSupported u) (hws : FutureSupported w) :
    kirchhoff coneMeasure (u + w) = kirchhoff coneMeasure u + kirchhoff coneMeasure w := by
  funext p
  rw [Pi.add_apply, kirchhoff_coneMeasure_apply (hu.add hw), kirchhoff_coneMeasure_apply hu,
    kirchhoff_coneMeasure_apply hw, ← mul_add,
    ← integral_add (integrable_kirchhoff_integrand_of_futureSupported hu hus p)
      (integrable_kirchhoff_integrand_of_futureSupported hw hws p)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [add_div]

/-- H3, Lemma 2: `(G⁺)^k` is additive on smooth future-supported functions. -/
theorem kpow_add {u w : Point → ℝ} (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hus : FutureSupported u) (hws : FutureSupported w) (k : ℕ) :
    kpow coneMeasure k (u + w) = kpow coneMeasure k u + kpow coneMeasure k w := by
  obtain ⟨K, hK, hKs⟩ := hus
  obtain ⟨K', hK', hK's⟩ := hws
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [kpow_succ, kpow_succ, kpow_succ, ih]
    have pu := And.intro (contDiff_kpow hu hK hKs k) (tsupport_kpow_subset hu hK hKs k)
    have pw := And.intro (contDiff_kpow hw hK' hK's k) (tsupport_kpow_subset hw hK' hK's k)
    exact kirchhoff_add_of_futureSupported pu.1.continuous pw.1.continuous ⟨K, hK, pu.2⟩
      ⟨K', hK', pw.2⟩

/-- H3, Lemma 2: `(G^±)^k` is homogeneous. -/
theorem kpow_smul (μ : Measure Point) (c : ℝ) (u : Point → ℝ) (k : ℕ) :
    kpow μ k (c • u) = c • kpow μ k u := by
  induction k with
  | zero => rfl
  | succ k ih => rw [kpow_succ, kpow_succ, ih, kirchhoff_smul]

/-- H3, Lemma 2: `(G^±)^{k+1} f = (G^±)^k (G^± f)`. -/
theorem kpow_succ' (μ : Measure Point) (k : ℕ) (f : Point → ℝ) :
    kpow μ (k + 1) f = kpow μ k (kirchhoff μ f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [kpow_succ, ih, ← kpow_succ]

/-! ### Proposition 3: convergence -/

/-- The data of the bounds for a test function: a time before which it vanishes, and a bound. -/
theorem exists_bound_data {f : Point → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) :
    ∃ t₀ C : ℝ, 0 ≤ C ∧ (∀ q : Point, q.1 < t₀ → f q = 0) ∧ ∀ q : Point, |f q| ≤ C := by
  obtain ⟨t₀, ht₀⟩ := exists_time_lower_bound hcf
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hcf
  refine ⟨t₀, C, (norm_nonneg (f 0)).trans (hC 0), fun q hq => ?_, fun q => hC q⟩
  by_contra hne
  exact absurd (ht₀ q (subset_tsupport _ hne)) (not_le.2 hq)

/-- H3, Proposition 3: the bound of the `k`-th term,
`|(−μ)^k (G⁺)^{k+1} f (p)| ≤ C τ² (√|μ| τ)^{2k}/(2k)!` with `τ = p⁰ − t₀ ≥ 0`. -/
theorem abs_gmu_term_le (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) {t₀ C : ℝ} (hC0 : 0 ≤ C) (h0 : ∀ q : Point, q.1 < t₀ → f q = 0)
    (hC : ∀ q : Point, |f q| ≤ C) (k : ℕ) {p : Point} (hp0 : t₀ ≤ p.1) :
    |(-μ) ^ k * kpow coneMeasure (k + 1) f p| ≤
      C * (p.1 - t₀) ^ 2 * ((Real.sqrt |μ| * (p.1 - t₀)) ^ (2 * k) / (2 * k).factorial) := by
  obtain ⟨K, hK, hKs⟩ := futureSupported_of_hasCompactSupport hcf
  have hb := abs_kpow_le hf hK hKs h0 (fun q _ => hC q) (k + 1) (le_refl p.1) hp0
  set τ := p.1 - t₀ with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
  have hfac : ((2 * k).factorial : ℝ) ≤ (2 * (k + 1)).factorial := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hμ : |(-μ) ^ k| = Real.sqrt |μ| ^ (2 * k) := by
    rw [abs_pow, abs_neg, pow_mul, Real.sq_sqrt (abs_nonneg μ)]
  rw [abs_mul, hμ]
  calc Real.sqrt |μ| ^ (2 * k) * |kpow coneMeasure (k + 1) f p|
      ≤ Real.sqrt |μ| ^ (2 * k) * (C * τ ^ (2 * (k + 1)) / (2 * (k + 1)).factorial) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ Real.sqrt |μ| ^ (2 * k) * (C * τ ^ (2 * (k + 1)) / (2 * k).factorial) := by
        gcongr
    _ = C * τ ^ 2 * ((Real.sqrt |μ| * τ) ^ (2 * k) / (2 * k).factorial) := by
        rw [mul_pow, show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
        ring

/-- H3, Proposition 3: the series for `G_μ⁺ f (p)` converges absolutely. -/
theorem summable_gmu (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (p : Point) : Summable fun k : ℕ => (-μ) ^ k * kpow coneMeasure (k + 1) f p := by
  obtain ⟨t₀, C, hC0, h0, hC⟩ := exists_bound_data hf.continuous hcf
  obtain ⟨K, hK, hKs⟩ := futureSupported_of_hasCompactSupport hcf
  by_cases hp : t₀ ≤ p.1
  · refine Summable.of_norm_bounded ((summable_cosh_series
      (Real.sqrt |μ| * (p.1 - t₀))).mul_left (C * (p.1 - t₀) ^ 2)) fun k => ?_
    rw [Real.norm_eq_abs]
    exact abs_gmu_term_le μ hf hcf hC0 h0 hC k hp
  · push Not at hp
    have : (fun k : ℕ => (-μ) ^ k * kpow coneMeasure (k + 1) f p) = fun _ => 0 := by
      funext k
      rw [kpow_eq_zero_of_lt hf hK hKs h0 (k + 1) hp, mul_zero]
    rw [this]
    exact summable_zero

/-- H3, Proposition 3: `G_μ⁺` is additive on test functions. -/
theorem gmu_add (μ : ℝ) {f g : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    gmu μ (f + g) = gmu μ f + gmu μ g := by
  funext p
  simp only [gmu, Pi.add_apply]
  rw [← (summable_gmu μ hf hcf p).tsum_add (summable_gmu μ hg hcg p)]
  congr 1
  funext k
  rw [kpow_add hf hg (futureSupported_of_hasCompactSupport hcf)
    (futureSupported_of_hasCompactSupport hcg), Pi.add_apply, mul_add]

/-- H3, Proposition 3: `G_μ⁺` is homogeneous. -/
theorem gmu_smul (μ c : ℝ) (f : Point → ℝ) : gmu μ (c • f) = c • gmu μ f := by
  funext p
  simp only [gmu, Pi.smul_apply, smul_eq_mul, kpow_smul]
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-! ### Proposition 4: smoothness -/

/-- The coordinate functionals `e^i` as continuous linear maps. -/
noncomputable def coordCLM (i : Fin 1 ⊕ Fin 3) : Point →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (stdBasis.coord i)

/-- A linear functional on `ℝ⁴` through its values on the basis: `L = Σ_i L(e_i) e^i`. -/
theorem clm_eq_sum (L : Point →L[ℝ] ℝ) : L = ∑ i, L (stdBasis i) • coordCLM i := by
  refine ContinuousLinearMap.ext fun v => ?_
  calc L v = L (∑ i, stdBasis.repr v i • stdBasis i) := by rw [stdBasis.sum_repr v]
    _ = ∑ i, stdBasis.repr v i * L (stdBasis i) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul]
    _ = (∑ i, L (stdBasis i) • coordCLM i) v := by
        simp [coordCLM, mul_comm]

/-- `∂ᵥ g` through the basis derivatives. -/
theorem dirDeriv_eq_sum {g : Point → ℝ} (hg : Differentiable ℝ g) (v : Point) :
    dirDeriv v g = ∑ i, coordCLM i v • dirDeriv (stdBasis i) g := by
  funext y
  have hL := clm_eq_sum (fderiv ℝ g y)
  simp only [dirDeriv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    (hg y).lineDeriv_eq_fderiv]
  conv_lhs => rw [hL]
  simp [mul_comm]

/-- A uniform version of the term bound, on `{p⁰ ≤ T}`. -/
theorem abs_gmu_term_le_of_le (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) {t₀ C : ℝ} (hC0 : 0 ≤ C) (h0 : ∀ q : Point, q.1 < t₀ → f q = 0)
    (hC : ∀ q : Point, |f q| ≤ C) (k : ℕ) {p : Point} {T : ℝ} (hpT : p.1 ≤ T) (hT : t₀ ≤ T) :
    |(-μ) ^ k * kpow coneMeasure (k + 1) f p| ≤
      C * (T - t₀) ^ 2 * ((Real.sqrt |μ| * (T - t₀)) ^ (2 * k) / (2 * k).factorial) := by
  obtain ⟨K, hK, hKs⟩ := futureSupported_of_hasCompactSupport hcf
  by_cases hp : t₀ ≤ p.1
  · refine (abs_gmu_term_le μ hf hcf hC0 h0 hC k hp).trans ?_
    have h1 : 0 ≤ p.1 - t₀ := by linarith
    have h2 : p.1 - t₀ ≤ T - t₀ := by linarith
    gcongr
  · push Not at hp
    rw [kpow_eq_zero_of_lt hf hK hKs h0 (k + 1) hp, mul_zero, abs_zero]
    have : 0 ≤ T - t₀ := by linarith
    positivity

/-- H3, Proposition 4(a): `G_μ⁺ f` has derivative `Σ_i G_μ⁺ (∂_{e_i} f)(x) e^i`. -/
theorem hasFDerivAt_gmu (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (x : Point) :
    HasFDerivAt (gmu μ f) (∑ i, gmu μ (dirDeriv (stdBasis i) f) x • coordCLM i) x := by
  obtain ⟨K, hK, hKs⟩ := futureSupported_of_hasCompactSupport hcf
  set g : Fin 1 ⊕ Fin 3 → Point → ℝ := fun i => dirDeriv (stdBasis i) f with hgdef
  have hg : ∀ i, ContDiff ℝ ∞ (g i) := fun i => contDiff_dirDeriv _ hf
  have hcg : ∀ i, HasCompactSupport (g i) := fun i => hasCompactSupport_dirDeriv _ hcf
  choose t C hC0 h0 hC using fun i => exists_bound_data (hg i).continuous (hcg i)
  set T : Fin 1 ⊕ Fin 3 → ℝ := fun i => max (x.1 + 1) (t i) with hTdef
  -- the terms and their derivatives
  set F : ℕ → Point → ℝ := fun n y => (-μ) ^ n * kpow coneMeasure (n + 1) f y with hF
  set F' : ℕ → Point → Point →L[ℝ] ℝ :=
    fun n y => ∑ i, ((-μ) ^ n * kpow coneMeasure (n + 1) (g i) y) • coordCLM i with hF'
  have hsm : ∀ n, ContDiff ℝ ∞ (F n) := fun n =>
    contDiff_const.mul (contDiff_kpow hf hK hKs (n + 1))
  have hder : ∀ n y, HasFDerivAt (F n) (F' n y) y := by
    intro n y
    have hd : DifferentiableAt ℝ (F n) y := (hsm n).differentiable (by simp) y
    convert hd.hasFDerivAt using 1
    rw [clm_eq_sum (fderiv ℝ (F n) y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← hd.lineDeriv_eq_fderiv]
    have hkd : Differentiable ℝ (kpow coneMeasure (n + 1) f) :=
      (contDiff_kpow hf hK hKs (n + 1)).differentiable (by simp)
    have e1 : lineDeriv ℝ (F n) y (stdBasis i) =
        dirDeriv (stdBasis i) ((-μ) ^ n • kpow coneMeasure (n + 1) f) y := rfl
    rw [e1, dirDeriv_smul _ _ hkd, Pi.smul_apply, smul_eq_mul, dirDeriv_kpow hf hK hKs]
  -- the uniform bounds on the unit ball about `x`
  have hbd : ∀ n y, y ∈ ball x 1 → ‖F' n y‖ ≤ ∑ i, (C i * (T i - t i) ^ 2 *
      ((Real.sqrt |μ| * (T i - t i)) ^ (2 * n) / (2 * n).factorial)) * ‖coordCLM i‖ := by
    intro n y hy
    have hy1 : y.1 ≤ x.1 + 1 := by
      have := (mem_ball.1 hy).le
      have h' : |y.1 - x.1| ≤ dist y x := by
        rw [Prod.dist_eq, Real.dist_eq]
        exact le_max_left _ _
      linarith [le_abs_self (y.1 - x.1)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact abs_gmu_term_le_of_le μ (hg i) (hcg i) (hC0 i) (h0 i) (hC i) n
      (hy1.trans (le_max_left _ _)) (le_max_right _ _)
  have hsum : Summable fun n : ℕ => ∑ i, (C i * (T i - t i) ^ 2 *
      ((Real.sqrt |μ| * (T i - t i)) ^ (2 * n) / (2 * n).factorial)) * ‖coordCLM i‖ :=
    summable_sum fun i _ =>
      (((summable_cosh_series _).mul_left _).mul_right _)
  have key := hasFDerivAt_tsum_of_isPreconnected hsum isOpen_ball
    (convex_ball x 1).isPreconnected (fun n y _ => hder n y) hbd (mem_ball_self one_pos)
    (summable_gmu μ hf hcf x) (mem_ball_self one_pos)
  have hlim : ∑' n, F' n x = ∑ i, gmu μ (g i) x • coordCLM i := by
    rw [Summable.tsum_finsetSum fun i _ => (summable_gmu μ (hg i) (hcg i) x).smul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (summable_gmu μ (hg i) (hcg i) x).tsum_smul_const _
  rw [hlim] at key
  exact key

/-- `G_μ⁺ 0 = 0`. -/
theorem gmu_zero_fun (μ : ℝ) : gmu μ 0 = 0 := by
  have := gmu_smul μ 0 (0 : Point → ℝ)
  simpa using this

/-- H3, Proposition 4: `G_μ⁺` of a finite combination. -/
theorem gmu_sum (μ : ℝ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) {g : ι → Point → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hcg : ∀ i, HasCompactSupport (g i)) :
    gmu μ (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • gmu μ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using gmu_zero_fun μ
  | insert a s ha ih =>
    have h1 : ContDiff ℝ ∞ (c a • g a) := (hg a).const_smul (c a)
    have h2 : HasCompactSupport (c a • g a) := (hcg a).smul_left
    have h3 : ContDiff ℝ ∞ (∑ i ∈ s, c i • g i) := by
      have := ContDiff.sum (s := s) fun i _ => (hg i).const_smul (c i)
      convert this using 1
      funext x
      simp [Finset.sum_apply]
    have h4 : HasCompactSupport (∑ i ∈ s, c i • g i) :=
      HasCompactSupport.finset_sum fun i _ => (hcg i).smul_left
    rw [Finset.sum_insert ha, Finset.sum_insert ha, gmu_add μ h1 h2 h3 h4, gmu_smul, ih]

/-- H3, Proposition 4(b): `∂ᵥ G_μ⁺ f = G_μ⁺ ∂ᵥ f`. -/
theorem dirDeriv_gmu (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (v : Point) : dirDeriv v (gmu μ f) = gmu μ (dirDeriv v f) := by
  funext x
  have hx := hasFDerivAt_gmu μ hf hcf x
  have e1 : dirDeriv v (gmu μ f) x =
      (∑ i, gmu μ (dirDeriv (stdBasis i) f) x • coordCLM i) v := (hx.hasLineDerivAt v).lineDeriv
  rw [e1, dirDeriv_eq_sum (hf.differentiable (by simp)) v,
    gmu_sum μ Finset.univ _ (fun i => contDiff_dirDeriv _ hf)
      (fun i => hasCompactSupport_dirDeriv _ hcf)]
  simp [mul_comm]

/-- H3, Proposition 4(c): `G_μ⁺ f` is smooth. -/
theorem contDiff_gmu (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) : ContDiff ℝ ∞ (gmu μ f) := by
  have key : ∀ n : ℕ, ∀ f : Point → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ContDiff ℝ n (gmu μ f) := by
    intro n
    induction n with
    | zero =>
      intro f hf hcf
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
        (hasFDerivAt_gmu μ hf hcf x).continuousAt)
    | succ n ih =>
      intro f hf hcf
      refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ?_, hasFDerivAt_gmu μ hf hcf⟩
      exact ContDiff.sum fun i _ =>
        (ih _ (contDiff_dirDeriv _ hf) (hasCompactSupport_dirDeriv _ hcf)).smul contDiff_const
  exact contDiff_infty.2 fun n => key n f hf hcf

/-! ### Theorem 5: the Green identities -/

/-- `∂ᵥ ∂ᵥ G_μ⁺ f = G_μ⁺ ∂ᵥ ∂ᵥ f`. -/
theorem dirDeriv_dirDeriv_gmu (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (v : Point) :
    dirDeriv v (dirDeriv v (gmu μ f)) = gmu μ (dirDeriv v (dirDeriv v f)) := by
  rw [dirDeriv_gmu μ hf hcf,
    dirDeriv_gmu μ (contDiff_dirDeriv _ hf) (hasCompactSupport_dirDeriv _ hcf)]

/-- `∂ᵥ ∂ᵥ f` is smooth when `f` is. -/
theorem contDiff_dirDeriv_dirDeriv {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (v : Point) :
    ContDiff ℝ ∞ (dirDeriv v (dirDeriv v f)) := contDiff_dirDeriv _ (contDiff_dirDeriv _ hf)

/-- `∂ᵥ ∂ᵥ f` has compact support when `f` has. -/
theorem hasCompactSupport_dirDeriv_dirDeriv {f : Point → ℝ} (hcf : HasCompactSupport f)
    (v : Point) :
    HasCompactSupport (dirDeriv v (dirDeriv v f)) :=
  hasCompactSupport_dirDeriv _ (hasCompactSupport_dirDeriv _ hcf)

/-- `□ G_μ⁺ f = G_μ⁺ □ f`. -/
theorem wave_gmu_eq (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    wave (gmu μ f) = gmu μ (wave f) := by
  set D : Fin 3 → Point → ℝ := fun i => dirDeriv (spaceDir i) (dirDeriv (spaceDir i) f) with hD
  have hs : gmu μ (∑ i, D i) = ∑ i, gmu μ (D i) := by
    have := gmu_sum μ Finset.univ (fun _ => (1 : ℝ)) (g := D)
      (fun i => contDiff_dirDeriv_dirDeriv hf _)
      (fun i => hasCompactSupport_dirDeriv_dirDeriv hcf _)
    simpa only [one_smul] using this
  have hS : ContDiff ℝ ∞ (∑ i, D i) := by
    have := ContDiff.sum (s := Finset.univ) fun i _ => contDiff_dirDeriv_dirDeriv hf (spaceDir i)
    convert this using 1
    funext x
    simp [hD, Finset.sum_apply]
  have hcS : HasCompactSupport (∑ i, D i) :=
    HasCompactSupport.finset_sum fun i _ => hasCompactSupport_dirDeriv_dirDeriv hcf _
  have hS' : ContDiff ℝ ∞ ((-1 : ℝ) • ∑ i, D i) := hS.const_smul (-1 : ℝ)
  have hcS' : HasCompactSupport ((-1 : ℝ) • ∑ i, D i) := hcS.smul_left
  have eb : wave f = dirDeriv timeDir (dirDeriv timeDir f) + (-1 : ℝ) • ∑ i, D i := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    rfl
  have eg : wave (gmu μ f) = dirDeriv timeDir (dirDeriv timeDir (gmu μ f)) +
      (-1 : ℝ) • ∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) (gmu μ f)) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    rfl
  rw [eb, eg, gmu_add μ (contDiff_dirDeriv_dirDeriv hf _)
    (hasCompactSupport_dirDeriv_dirDeriv hcf _) hS' hcS', gmu_smul, hs,
    dirDeriv_dirDeriv_gmu μ hf hcf]
  congr 2
  exact Finset.sum_congr rfl fun i _ => dirDeriv_dirDeriv_gmu μ hf hcf _

/-- The shifted series `Σ_k (−μ)^k (G⁺)^k f` converges. -/
theorem summable_gmu_shift (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (p : Point) :
    Summable fun k : ℕ => (-μ) ^ k * kpow coneMeasure k f p := by
  refine (summable_nat_add_iff 1).1 ?_
  have := (summable_gmu μ hf hcf p).mul_left (-μ)
  refine this.congr fun k => ?_
  simp only [pow_succ]
  ring

/-- `G_μ⁺ □ f = f − μ G_μ⁺ f`, by telescoping. -/
theorem gmu_wave_eq (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    gmu μ (wave f) = f - μ • gmu μ f := by
  funext p
  have hG : kirchhoff coneMeasure (wave f) = f :=
    kirchhoff_wave_of_futureSupported hf (futureSupported_of_hasCompactSupport hcf)
  have e1 : gmu μ (wave f) p = ∑' k : ℕ, (-μ) ^ k * kpow coneMeasure k f p := by
    unfold gmu
    congr 1
    funext k
    rw [kpow_succ', hG]
  have e2 : ∑' k : ℕ, (-μ) ^ (k + 1) * kpow coneMeasure (k + 1) f p = -μ * gmu μ f p := by
    rw [gmu, ← tsum_mul_left]
    congr 1
    funext k
    ring
  rw [e1, (summable_gmu_shift μ hf hcf p).tsum_eq_zero_add, e2]
  simp only [pow_zero, one_mul, kpow_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- H3, Theorem 5: `(□ + μ) G_μ⁺ f = f`. -/
theorem wave_gmu (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    wave (gmu μ f) + μ • gmu μ f = f := by
  rw [wave_gmu_eq μ hf hcf, gmu_wave_eq μ hf hcf, sub_add_cancel]

/-- H3, Theorem 5: `G_μ⁺ (□ + μ) f = f`. -/
theorem gmu_kg (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    gmu μ (wave f + μ • f) = f := by
  have h1 : ContDiff ℝ ∞ (wave f) := contDiff_wave hf
  have h2 : HasCompactSupport (wave f) :=
    hcf.mono' ((subset_tsupport _).trans (tsupport_wave_subset f))
  have h3 : ContDiff ℝ ∞ (μ • f) := hf.const_smul μ
  have h4 : HasCompactSupport (μ • f) := hcf.smul_left
  rw [gmu_add μ h1 h2 h3 h4, gmu_smul, gmu_wave_eq μ hf hcf, sub_add_cancel]

/-! ### Proposition 6: supports -/

/-- H3, Proposition 6: `supp G_μ⁺ f ⊆ J⁺(supp f)`. -/
theorem tsupport_gmu_subset (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) : tsupport (gmu μ f) ⊆ Jplus (tsupport f) := by
  have hKs : tsupport f ⊆ Jplus (tsupport f) := fun q hq => ⟨q, hq, causalLE_refl q⟩
  refine closure_minimal (fun p hp => ?_) (isClosed_Jplus hcf)
  by_contra hn
  apply hp
  have hz : ∀ k : ℕ, (-μ) ^ k * kpow coneMeasure (k + 1) f p = 0 := by
    intro k
    by_contra hne
    exact hn ((tsupport_kpow_subset hf hcf hKs (k + 1))
      (subset_tsupport _ (right_ne_zero_of_mul hne)))
  simp only [gmu, hz, tsum_zero]

/-! ### Proposition 7: the advanced series -/

/-- `(G⁻)^k f = ((G⁺)^k (f ∘ R)) ∘ R`. -/
theorem kpowPast_eq {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (k : ℕ) :
    kpow coneMeasurePast k f = kpow coneMeasure k (f ∘ timeRefl) ∘ timeRefl := by
  have hR : ContDiff ℝ ∞ (f ∘ timeRefl) := hf.comp contDiff_timeRefl
  have hcR : HasCompactSupport (f ∘ timeRefl) := hcf.comp_homeomorph timeReflHomeo
  have hKs : tsupport (f ∘ timeRefl) ⊆ Jplus (tsupport (f ∘ timeRefl)) :=
    fun q hq => ⟨q, hq, causalLE_refl q⟩
  induction k with
  | zero =>
    funext p
    simp
  | succ k ih =>
    rw [kpow_succ, kpow_succ, ih, kirchhoffPast_eq_comp
      (((contDiff_kpow hR hcR hKs k).continuous).comp continuous_timeRefl)]
    funext p
    simp only [Function.comp_apply]
    congr 1
    funext q
    simp

/-- H3, Proposition 7: `G_μ⁻ f (p) = G_μ⁺ (f ∘ R)(R p)`. -/
theorem gmuPast_eq (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    gmuPast μ f = gmu μ (f ∘ timeRefl) ∘ timeRefl := by
  funext p
  simp only [gmuPast, gmu, Function.comp_apply, kpowPast_eq hf hcf]

/-- H3, Proposition 7: the advanced series converges absolutely. -/
theorem summable_gmuPast (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (p : Point) :
    Summable fun k : ℕ => (-μ) ^ k * kpow coneMeasurePast (k + 1) f p := by
  have := summable_gmu μ (hf.comp contDiff_timeRefl) (hcf.comp_homeomorph timeReflHomeo)
    (timeRefl p)
  refine this.congr fun k => ?_
  rw [kpowPast_eq hf hcf]
  rfl

/-- H3, Proposition 7: `∂ᵥ G_μ⁻ f = G_μ⁻ ∂ᵥ f`. -/
theorem dirDeriv_gmuPast (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (v : Point) :
    dirDeriv v (gmuPast μ f) = gmuPast μ (dirDeriv v f) := by
  have hR := hf.comp contDiff_timeRefl
  have hcR : HasCompactSupport (f ∘ timeRefl) := hcf.comp_homeomorph timeReflHomeo
  rw [gmuPast_eq μ hf hcf, gmuPast_eq μ (contDiff_dirDeriv v hf) (hasCompactSupport_dirDeriv v hcf),
    dirDeriv_comp_timeRefl, dirDeriv_gmu μ hR hcR, dirDeriv_comp_timeRefl, timeRefl_timeRefl]

/-- H3, Proposition 7: `G_μ⁻` is additive on test functions. -/
theorem gmuPast_add (μ : ℝ) {f g : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    gmuPast μ (f + g) = gmuPast μ f + gmuPast μ g := by
  have hs : ContDiff ℝ ∞ (f + g) := hf.add hg
  have hcs : HasCompactSupport (f + g) := hcf.add hcg
  rw [gmuPast_eq μ hs hcs, gmuPast_eq μ hf hcf, gmuPast_eq μ hg hcg]
  have hfg : (f + g) ∘ timeRefl = f ∘ timeRefl + g ∘ timeRefl := rfl
  rw [hfg, gmu_add μ (hf.comp contDiff_timeRefl) (hcf.comp_homeomorph timeReflHomeo)
    (hg.comp contDiff_timeRefl) (hcg.comp_homeomorph timeReflHomeo)]
  rfl

/-- H3, Proposition 7: `G_μ⁻` is homogeneous. -/
theorem gmuPast_smul (μ c : ℝ) (f : Point → ℝ) : gmuPast μ (c • f) = c • gmuPast μ f := by
  funext p
  simp only [gmuPast, Pi.smul_apply, smul_eq_mul, kpow_smul]
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- H3, Proposition 7: `G_μ⁻ f` is smooth. -/
theorem contDiff_gmuPast (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) : ContDiff ℝ ∞ (gmuPast μ f) := by
  rw [gmuPast_eq μ hf hcf]
  exact (contDiff_gmu μ (hf.comp contDiff_timeRefl) (hcf.comp_homeomorph timeReflHomeo)).comp
    contDiff_timeRefl

/-- H3, Proposition 7: `(□ + μ) G_μ⁻ f = f`. -/
theorem wave_gmuPast (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    wave (gmuPast μ f) + μ • gmuPast μ f = f := by
  have hR := hf.comp contDiff_timeRefl
  have hcR : HasCompactSupport (f ∘ timeRefl) := hcf.comp_homeomorph timeReflHomeo
  rw [gmuPast_eq μ hf hcf, wave_comp_timeRefl (contDiff_gmu μ hR hcR)]
  have := wave_gmu μ hR hcR
  funext p
  have hp := congrFun this (timeRefl p)
  simpa using hp

/-- H3, Proposition 7: `G_μ⁻ (□ + μ) f = f`. -/
theorem gmuPast_kg (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    gmuPast μ (wave f + μ • f) = f := by
  have hR := hf.comp contDiff_timeRefl
  have hcR : HasCompactSupport (f ∘ timeRefl) := hcf.comp_homeomorph timeReflHomeo
  have hμf : ContDiff ℝ ∞ (μ • f) := hf.const_smul μ
  have hb : ContDiff ℝ ∞ (wave f + μ • f) := (contDiff_wave hf).add hμf
  have hcb : HasCompactSupport (wave f + μ • f) :=
    (hcf.mono' ((subset_tsupport _).trans (tsupport_wave_subset f))).add
      hcf.smul_left
  rw [gmuPast_eq μ hb hcb]
  have e : (wave f + μ • f) ∘ timeRefl = wave (f ∘ timeRefl) + μ • (f ∘ timeRefl) := by
    rw [wave_comp_timeRefl hf]
    rfl
  rw [e, gmu_kg μ hR hcR]
  funext p
  simp

/-- H3, Proposition 7: `supp G_μ⁻ f ⊆ J⁻(supp f)`. -/
theorem tsupport_gmuPast_subset (μ : ℝ) {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) : tsupport (gmuPast μ f) ⊆ Jminus (tsupport f) := by
  have hR := hf.comp contDiff_timeRefl
  have hcR : HasCompactSupport (f ∘ timeRefl) := hcf.comp_homeomorph timeReflHomeo
  refine closure_minimal (fun p hp => ?_) (isClosed_Jminus hcf)
  rw [gmuPast_eq μ hf hcf] at hp
  obtain ⟨k, hk, hkp⟩ := tsupport_gmu_subset μ hR hcR (subset_tsupport _ hp)
  have hk' : timeRefl k ∈ tsupport f := by
    have := tsupport_comp_eq_preimage f timeReflHomeo
    change k ∈ tsupport (f ∘ timeReflHomeo) at hk
    rw [this] at hk
    exact hk
  refine ⟨timeRefl k, hk', ?_⟩
  have := (causalLE_timeRefl (p := timeRefl k) (q := p)).1
  simp only [timeRefl_timeRefl] at this
  exact this hkp

/-! ### Proposition 8: adjointness -/

/-- `∫ u (G⁺)^n v = ∫ ((G⁻)^n u) v` for `u` past-supported and `v` future-supported. -/
theorem integral_mul_kpow_eq {u v : Point → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hus : PastSupported u) (hvs : FutureSupported v) (n : ℕ) :
    ∫ p, u p * kpow coneMeasure n v p = ∫ p, kpow coneMeasurePast n u p * v p := by
  obtain ⟨K, hK, hKs⟩ := hvs
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    obtain ⟨K', hK', hK's⟩ := hus
    have pv := And.intro (contDiff_kpow hv hK hKs n) (tsupport_kpow_subset hv hK hKs n)
    rw [kpow_succ, (integral_mul_kirchhoff_eq hu pv.1 ⟨K', hK', hK's⟩ ⟨K, hK, pv.2⟩).2.2,
      ih (contDiff_kirchhoffPast_of_pastSupported hu ⟨K', hK', hK's⟩)
        ⟨K', hK', tsupport_kirchhoffPast_subset hu.continuous hK' hK's⟩, kpow_succ']

/-- A compact set has a latest time. -/
theorem exists_time_upper_bound {K : Set Point} (hK : IsCompact K) :
    ∃ T : ℝ, ∀ k ∈ K, k.1 ≤ T := by
  obtain ⟨T, hT⟩ := hK.bddAbove_image continuous_fst.continuousOn
  exact ⟨T, fun k hk => hT ⟨k, hk, rfl⟩⟩

/-- H3, Proposition 8: `⟨f, G_μ⁺ g⟩ = ⟨g, G_μ⁻ f⟩`. -/
theorem integral_mul_gmu (μ : ℝ) {f g : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ∫ p, f p * gmu μ g p = ∫ p, gmuPast μ f p * g p := by
  have hR := hf.comp contDiff_timeRefl
  have hcR : HasCompactSupport (f ∘ timeRefl) := hcf.comp_homeomorph timeReflHomeo
  have hKg : tsupport g ⊆ Jplus (tsupport g) := fun q hq => ⟨q, hq, causalLE_refl q⟩
  have hKR : tsupport (f ∘ timeRefl) ⊆ Jplus (tsupport (f ∘ timeRefl)) :=
    fun q hq => ⟨q, hq, causalLE_refl q⟩
  -- the retarded side
  obtain ⟨tg, Cg, hCg0, h0g, hCg⟩ := exists_bound_data hg.continuous hcg
  obtain ⟨Tf, hTf⟩ := exists_time_upper_bound hcf
  have lhs : ∫ p, f p * gmu μ g p =
      ∑' k : ℕ, ∫ p, f p * ((-μ) ^ k * kpow coneMeasure (k + 1) g p) :=
    integral_mul_tsum_eq hf.continuous hcf
      (fun k => continuous_const.mul (contDiff_kpow hg hcg hKg (k + 1)).continuous)
      ((summable_cosh_series (Real.sqrt |μ| * (max Tf tg - tg))).mul_left
        (Cg * (max Tf tg - tg) ^ 2))
      fun k p hp => abs_gmu_term_le_of_le μ hg hcg hCg0 h0g hCg k
        ((hTf p hp).trans (le_max_left _ _)) (le_max_right _ _)
  -- the advanced side, through the reflection
  obtain ⟨tf, Cf, hCf0, h0f, hCf⟩ := exists_bound_data hR.continuous hcR
  obtain ⟨tg', htg'⟩ := exists_time_lower_bound hcg
  have hpast : ∀ k p, kpow coneMeasurePast (k + 1) f p =
      kpow coneMeasure (k + 1) (f ∘ timeRefl) (timeRefl p) := fun k p => by
    rw [kpowPast_eq hf hcf]
    rfl
  have rhs : ∫ p, gmuPast μ f p * g p =
      ∑' k : ℕ, ∫ p, g p * ((-μ) ^ k * kpow coneMeasurePast (k + 1) f p) := by
    have e : ∫ p, gmuPast μ f p * g p = ∫ p, g p * gmuPast μ f p := by
      congr 1
      funext p
      ring
    rw [e]
    refine integral_mul_tsum_eq hg.continuous hcg (fun k => ?_)
      ((summable_cosh_series (Real.sqrt |μ| * (max (-tg') tf - tf))).mul_left
        (Cf * (max (-tg') tf - tf) ^ 2)) fun k p hp => ?_
    · rw [kpowPast_eq hf hcf]
      exact continuous_const.mul
        (((contDiff_kpow hR hcR hKR (k + 1)).continuous).comp continuous_timeRefl)
    · rw [hpast]
      refine abs_gmu_term_le_of_le μ hR hcR hCf0 h0f hCf k ?_ (le_max_right _ _)
      have := htg' p hp
      simp only [timeRefl]
      linarith [le_max_left (-tg') tf]
  rw [lhs, rhs]
  refine tsum_congr fun k => ?_
  have e1 : ∫ p, f p * ((-μ) ^ k * kpow coneMeasure (k + 1) g p) =
      (-μ) ^ k * ∫ p, f p * kpow coneMeasure (k + 1) g p := by
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  have e2 : ∫ p, g p * ((-μ) ^ k * kpow coneMeasurePast (k + 1) f p) =
      (-μ) ^ k * ∫ p, kpow coneMeasurePast (k + 1) f p * g p := by
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  rw [e1, e2, integral_mul_kpow_eq hf hg (pastSupported_of_hasCompactSupport hcf)
    (futureSupported_of_hasCompactSupport hcg)]

/-! ### Corollary 9: `μ = 0` -/

/-- H3, Corollary 9: `G_0⁺ = G⁺`. -/
theorem gmu_zero (f : Point → ℝ) : gmu 0 f = kirchhoff coneMeasure f := by
  funext p
  rw [gmu, tsum_eq_single 0 fun k hk => by simp [zero_pow hk]]
  simp [kpow_succ]

/-- H3, Corollary 9: `G_0⁻ = G⁻`. -/
theorem gmuPast_zero (f : Point → ℝ) : gmuPast 0 f = kirchhoff coneMeasurePast f := by
  funext p
  rw [gmuPast, tsum_eq_single 0 fun k hk => by simp [zero_pow hk]]
  simp [kpow_succ]

end LinearAQFT.Minkowski
