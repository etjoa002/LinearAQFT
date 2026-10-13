/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Cutoff
import LinearAQFT.Minkowski.Core

/-!
# The Kirchhoff operators beyond test functions, and the power bound

Stage H, milestone H2 (Definition 1, Lemmas 2, 3, 5, Proposition 4, Corollary 6, Proposition 7).
`G⁺ h (p)` samples `h` only on the causal past of `p`, so a smooth `h` supported in the causal
future `J⁺(K)` of a compact set agrees, near the past of any bounded region, with a test function
`ψ h`; the stage-G results for test functions then carry over. The power bound
`|(G⁺)^k h| ≤ C (t − t₀)^{2k}/(2k)!` makes the series of stage H converge. The advanced operator is
reduced to the retarded one by the time reflection `R(t, x) = (−t, x)`.

## Main results

* `FutureSupported`, `PastSupported` (Definition 1).
* `kirchhoff_congr_of_eqOn`, `kirchhoffPast_congr_of_eqOn` (Lemma 2).
* `exists_cutoff`, `cutoff_eventuallyEq` (Lemma 3).
* `contDiff_kirchhoff_of_futureSupported`, `dirDeriv_kirchhoff_of_futureSupported`,
  `tsupport_kirchhoff_subset`, `wave_kirchhoff_of_futureSupported`,
  `kirchhoff_wave_of_futureSupported` and their advanced forms (Proposition 4).
* `abs_kirchhoff_le`, `integral_mul_sub_pow` (Lemma 5); `abs_kpow_le` (Corollary 6).
* `integral_mul_kirchhoff_eq` (Proposition 7).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology Manifold
open MeasureTheory Set Filter Function Metric

/-! ### Definition 1 -/

/-- H2, Definition 1: `h` is supported in the causal future of a compact set. -/
def FutureSupported (h : Point → ℝ) : Prop :=
  ∃ K : Set Point, IsCompact K ∧ tsupport h ⊆ Jplus K

/-- H2, Definition 1: `h` is supported in the causal past of a compact set. -/
def PastSupported (h : Point → ℝ) : Prop :=
  ∃ K : Set Point, IsCompact K ∧ tsupport h ⊆ Jminus K

/-! ### Lemma 2: causality -/

theorem sample_mem_Jminus (p : Point) (y : Space) : (p.1 - ‖y‖, p.2 - y) ∈ Jminus {p} :=
  ⟨p, rfl, by
    change ‖p.2 - (p.2 - y)‖ ≤ p.1 - (p.1 - ‖y‖)
    simp⟩

theorem sample_mem_Jplus (p : Point) (y : Space) : (p.1 + ‖y‖, p.2 - y) ∈ Jplus {p} :=
  ⟨p, rfl, by
    change ‖(p.2 - y) - p.2‖ ≤ (p.1 + ‖y‖) - p.1
    simp⟩

/-- H2, Lemma 2: `G⁺ h (p)` depends only on `h` on the causal past of `p`. -/
theorem kirchhoff_congr_of_eqOn {h h' : Point → ℝ} (hh : Continuous h) (hh' : Continuous h')
    {p : Point} (heq : EqOn h h' (Jminus {p})) :
    kirchhoff coneMeasure h p = kirchhoff coneMeasure h' p := by
  rw [kirchhoff_coneMeasure_apply hh, kirchhoff_coneMeasure_apply hh']
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [heq (sample_mem_Jminus p y)]

/-- H2, Lemma 2: `G⁻ h (p)` depends only on `h` on the causal future of `p`. -/
theorem kirchhoffPast_congr_of_eqOn {h h' : Point → ℝ} (hh : Continuous h)
    (hh' : Continuous h') {p : Point} (heq : EqOn h h' (Jplus {p})) :
    kirchhoff coneMeasurePast h p = kirchhoff coneMeasurePast h' p := by
  rw [kirchhoff_coneMeasurePast_apply hh, kirchhoff_coneMeasurePast_apply hh']
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [heq (sample_mem_Jplus p y)]

/-! ### Time reflection -/

/-- The time reflection `R(t, x) = (−t, x)`. -/
def timeRefl (q : Point) : Point := (-q.1, q.2)

@[simp] theorem timeRefl_timeRefl (q : Point) : timeRefl (timeRefl q) = q := by
  simp [timeRefl]

theorem continuous_timeRefl : Continuous timeRefl := by
  unfold timeRefl
  fun_prop

theorem contDiff_timeRefl : ContDiff ℝ ∞ timeRefl :=
  (contDiff_fst.neg).prodMk contDiff_snd

/-- `R` reverses the causal order. -/
theorem causalLE_timeRefl {p q : Point} :
    causalLE (timeRefl p) (timeRefl q) ↔ causalLE q p := by
  unfold causalLE timeRefl
  simp only
  rw [norm_sub_rev]
  constructor <;> intro h <;> linarith

/-- H2, Proposition 4 (the advanced case): `G⁻ h = (G⁺ (h ∘ R)) ∘ R`. -/
theorem kirchhoffPast_eq {h : Point → ℝ} (hh : Continuous h) (p : Point) :
    kirchhoff coneMeasurePast h p = kirchhoff coneMeasure (h ∘ timeRefl) (timeRefl p) := by
  rw [kirchhoff_coneMeasurePast_apply hh,
    kirchhoff_coneMeasure_apply (hh.comp continuous_timeRefl)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, timeRefl]
  congr 3
  ring

/-! ### Lemma 3: cutting off -/

/-- H2, Lemma 3: for a compact set `A` there is a test function equal to `1` on the
`1`-neighbourhood of `A`. -/
theorem exists_cutoff {A : Set Point} (hA : IsCompact A) :
    ∃ ψ : TestFun, ∀ q ∈ thickening 1 A, ψ q = 1 := by
  obtain ⟨ψ, hψs, hψc, hone⟩ := exists_smooth_cutoff hA
  exact ⟨⟨ψ, hψs, hψc, by simp⟩, hone⟩

/-- H2, Lemma 3: if `supp h ⊆ J⁺(K)` and `ψ = 1` near `J⁺(K) ∩ J⁻(Ū)`, then `ψ h = h` near
every point of the causal past of every `p ∈ U`. -/
theorem cutoff_eventuallyEq {K U : Set Point} {h : Point → ℝ} (hs : tsupport h ⊆ Jplus K)
    {ψ : Point → ℝ} (hψ : ∀ q ∈ thickening 1 (Jplus K ∩ Jminus (closure U)), ψ q = 1)
    {p : Point} (hp : p ∈ U) {q : Point} (hq : q ∈ Jminus {p}) :
    (fun r => ψ r * h r) =ᶠ[𝓝 q] h := by
  obtain ⟨_, rfl, hqp⟩ := hq
  by_cases hqs : q ∈ tsupport h
  · have hqA : q ∈ Jplus K ∩ Jminus (closure U) := ⟨hs hqs, _, subset_closure hp, hqp⟩
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening one_pos _ hqA)] with r hr
    rw [hψ r hr, one_mul]
  · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hqs] with r hr
    simp only [Pi.zero_apply] at hr
    simp [hr]

/-- The localization used throughout: near `p₀`, `G⁺ h = G⁺ (ψ h)` for a test function `ψ`
with `ψ h = h` near the causal past of every point of the unit ball about `p₀`. -/
theorem exists_localization {h : Point → ℝ} (hh : Continuous h) {K : Set Point}
    (hK : IsCompact K) (hs : tsupport h ⊆ Jplus K) (p₀ : Point) :
    ∃ ψ : TestFun, (∀ p ∈ ball p₀ 1, ∀ q ∈ Jminus {p}, (fun r => ψ r * h r) =ᶠ[𝓝 q] h) ∧
      ∀ p ∈ ball p₀ 1, kirchhoff coneMeasure h p =
        kirchhoff coneMeasure (fun r => ψ r * h r) p := by
  have hA : IsCompact (Jplus K ∩ Jminus (closure (ball p₀ 1))) :=
    isCompact_Jplus_inter_Jminus hK
      ((isCompact_closedBall p₀ 1).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall)
  obtain ⟨ψ, hψ⟩ := exists_cutoff hA
  have hev := fun p (hp : p ∈ ball p₀ 1) q (hq : q ∈ Jminus {p}) =>
    cutoff_eventuallyEq (U := ball p₀ 1) hs hψ hp hq
  refine ⟨ψ, hev, fun p hp => ?_⟩
  exact (kirchhoff_congr_of_eqOn ((ψ.continuous).mul hh) hh
    fun q hq => (hev p hp q hq).eq_of_nhds).symm

/-! ### Proposition 4: `G⁺` on future-supported functions -/

/-- `ψ h` as a test function. -/
noncomputable def cutoffTest (ψ : TestFun) {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) : TestFun :=
  ⟨fun r => ψ r * h r, ψ.contDiff.mul hh, ψ.hasCompactSupport.mul_right, by simp⟩

@[simp] theorem cutoffTest_apply (ψ : TestFun) {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) (r : Point) :
    cutoffTest ψ hh r = ψ r * h r := rfl

/-- H2, Proposition 4(a): `G⁺ h` is smooth. -/
theorem contDiff_kirchhoff_of_futureSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : FutureSupported h) : ContDiff ℝ ∞ (kirchhoff coneMeasure h) := by
  obtain ⟨K, hK, hKs⟩ := hs
  refine contDiff_iff_contDiffAt.2 fun p₀ => ?_
  obtain ⟨ψ, -, heq⟩ := exists_localization hh.continuous hK hKs p₀
  have hsm : ContDiff ℝ ∞ (kirchhoff coneMeasure (fun r => ψ r * h r)) :=
    contDiff_kirchhoff coneMeasure (cutoffTest ψ hh).contDiff (cutoffTest ψ hh).hasCompactSupport
  refine hsm.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with p hp
  exact heq p hp

/-- H2, Proposition 4(b): `∂ᵥ G⁺ h = G⁺ ∂ᵥ h`. -/
theorem dirDeriv_kirchhoff_of_futureSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : FutureSupported h) (v : Point) :
    dirDeriv v (kirchhoff coneMeasure h) = kirchhoff coneMeasure (dirDeriv v h) := by
  obtain ⟨K, hK, hKs⟩ := hs
  funext p₀
  obtain ⟨ψ, hev, heq⟩ := exists_localization hh.continuous hK hKs p₀
  have hloc : kirchhoff coneMeasure h =ᶠ[𝓝 p₀] kirchhoff coneMeasure (fun r => ψ r * h r) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with p hp
    exact heq p hp
  rw [(dirDeriv_eventuallyEq hloc v).eq_of_nhds]
  change dirDeriv v (kirchhoff coneMeasure (cutoffTest ψ hh)) p₀ = _
  rw [dirDeriv_kirchhoff coneMeasure (cutoffTest ψ hh).contDiff
      (cutoffTest ψ hh).hasCompactSupport v]
  refine kirchhoff_congr_of_eqOn (contDiff_dirDeriv v (cutoffTest ψ hh).contDiff).continuous
    (contDiff_dirDeriv v hh).continuous fun q hq => ?_
  exact (dirDeriv_eventuallyEq (hev p₀ (mem_ball_self one_pos) q hq) v).eq_of_nhds

/-- H2, Proposition 4(c): `supp G⁺ h ⊆ J⁺(K)` when `supp h ⊆ J⁺(K)`. -/
theorem tsupport_kirchhoff_subset {h : Point → ℝ} (hh : Continuous h) {K : Set Point}
    (hK : IsCompact K) (hs : tsupport h ⊆ Jplus K) :
    tsupport (kirchhoff coneMeasure h) ⊆ Jplus K := by
  refine closure_minimal (fun p hp => ?_) (isClosed_Jplus hK)
  by_contra hn
  apply hp
  have h0 : kirchhoff coneMeasure h p = kirchhoff coneMeasure (fun _ => (0 : ℝ)) p := by
    refine kirchhoff_congr_of_eqOn hh continuous_const fun q hq => ?_
    by_contra hne
    obtain ⟨k, hk, hkq⟩ := hs (subset_tsupport _ hne)
    obtain ⟨_, rfl, hqp⟩ := hq
    exact hn ⟨k, hk, causalLE_trans hkq hqp⟩
  rw [h0, kirchhoff_apply]
  simp

/-- H2, Proposition 4(d): `□ G⁺ h = h`. -/
theorem wave_kirchhoff_of_futureSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : FutureSupported h) : wave (kirchhoff coneMeasure h) = h := by
  obtain ⟨K, hK, hKs⟩ := hs
  funext p₀
  obtain ⟨ψ, hev, heq⟩ := exists_localization hh.continuous hK hKs p₀
  have hloc : kirchhoff coneMeasure h =ᶠ[𝓝 p₀] kirchhoff coneMeasure (fun r => ψ r * h r) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with p hp
    exact heq p hp
  have hG : wave (kirchhoff coneMeasure (fun r => ψ r * h r)) = fun r => ψ r * h r :=
    congrArg Subtype.val (waveF_gret_eq (cutoffTest ψ hh))
  rw [wave_congr_of_eventuallyEq hloc, hG]
  exact (hev p₀ (mem_ball_self one_pos) p₀ ⟨p₀, rfl, causalLE_refl p₀⟩).eq_of_nhds

/-- H2, Proposition 4(d): `G⁺ □ h = h`. -/
theorem kirchhoff_wave_of_futureSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : FutureSupported h) : kirchhoff coneMeasure (wave h) = h := by
  obtain ⟨K, hK, hKs⟩ := hs
  funext p₀
  obtain ⟨ψ, hev, -⟩ := exists_localization hh.continuous hK hKs p₀
  have hG : kirchhoff coneMeasure (wave (fun r => ψ r * h r)) = fun r => ψ r * h r :=
    congrArg Subtype.val (gret_waveD (cutoffTest ψ hh))
  have hc : kirchhoff coneMeasure (wave h) p₀ =
      kirchhoff coneMeasure (wave (fun r => ψ r * h r)) p₀ := by
    refine kirchhoff_congr_of_eqOn (contDiff_wave hh).continuous
      (contDiff_wave (cutoffTest ψ hh).contDiff).continuous fun q hq => ?_
    exact (wave_congr_of_eventuallyEq (hev p₀ (mem_ball_self one_pos) q hq)).symm
  rw [hc, hG]
  exact (hev p₀ (mem_ball_self one_pos) p₀ ⟨p₀, rfl, causalLE_refl p₀⟩).eq_of_nhds

/-! ### Proposition 4, the advanced case, by time reflection -/

/-- The time reflection as a homeomorphism. -/
def timeReflHomeo : Point ≃ₜ Point where
  toFun := timeRefl
  invFun := timeRefl
  left_inv := timeRefl_timeRefl
  right_inv := timeRefl_timeRefl
  continuous_toFun := continuous_timeRefl
  continuous_invFun := continuous_timeRefl

theorem timeRefl_add_smul (q v : Point) (s : ℝ) :
    timeRefl (q + s • v) = timeRefl q + s • timeRefl v := by
  refine Prod.ext ?_ rfl
  simp only [timeRefl, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  ring

theorem dirDeriv_comp_timeRefl (v : Point) (g : Point → ℝ) :
    dirDeriv v (g ∘ timeRefl) = dirDeriv (timeRefl v) g ∘ timeRefl := by
  funext q
  simp only [dirDeriv, lineDeriv, Function.comp_apply, timeRefl_add_smul]

theorem wave_comp_timeRefl {g : Point → ℝ} (hg : ContDiff ℝ ∞ g) :
    wave (g ∘ timeRefl) = wave g ∘ timeRefl := by
  have e : (g ∘ timeRefl) = fun q : Point => g (0 + ((-1) * q.1, (1 : ℝ) • q.2)) := by
    funext q
    simp [timeRefl]
  have e' : (wave g ∘ timeRefl) = fun q : Point => wave g (0 + ((-1) * q.1, (1 : ℝ) • q.2)) := by
    funext q
    simp [timeRefl]
  rw [e, e', wave_comp_reflect hg 0 (by norm_num) (by norm_num)]

/-- The time reflection maps past-supported functions to future-supported ones. -/
theorem PastSupported.comp_timeRefl {h : Point → ℝ} (hs : PastSupported h) :
    FutureSupported (h ∘ timeRefl) := by
  obtain ⟨K, hK, hKs⟩ := hs
  refine ⟨timeRefl '' K, hK.image continuous_timeRefl, fun q hq => ?_⟩
  have hq' : timeRefl q ∈ tsupport h := by
    have := tsupport_comp_eq_preimage h timeReflHomeo
    change q ∈ tsupport (h ∘ timeReflHomeo) at hq
    rw [this] at hq
    exact hq
  obtain ⟨k, hk, hqk⟩ := hKs hq'
  refine ⟨timeRefl k, ⟨k, hk, rfl⟩, ?_⟩
  have := (causalLE_timeRefl (p := k) (q := timeRefl q)).2 hqk
  simpa using this

theorem kirchhoffPast_eq_comp {h : Point → ℝ} (hh : Continuous h) :
    kirchhoff coneMeasurePast h = kirchhoff coneMeasure (h ∘ timeRefl) ∘ timeRefl :=
  funext fun p => kirchhoffPast_eq hh p

/-- H2, Proposition 4(a), advanced. -/
theorem contDiff_kirchhoffPast_of_pastSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : PastSupported h) : ContDiff ℝ ∞ (kirchhoff coneMeasurePast h) := by
  rw [kirchhoffPast_eq_comp hh.continuous]
  exact (contDiff_kirchhoff_of_futureSupported (hh.comp contDiff_timeRefl)
    hs.comp_timeRefl).comp contDiff_timeRefl

/-- H2, Proposition 4(b), advanced. -/
theorem dirDeriv_kirchhoffPast_of_pastSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : PastSupported h) (v : Point) :
    dirDeriv v (kirchhoff coneMeasurePast h) = kirchhoff coneMeasurePast (dirDeriv v h) := by
  rw [kirchhoffPast_eq_comp hh.continuous,
    kirchhoffPast_eq_comp (contDiff_dirDeriv v hh).continuous, dirDeriv_comp_timeRefl,
    dirDeriv_kirchhoff_of_futureSupported (hh.comp contDiff_timeRefl) hs.comp_timeRefl,
    dirDeriv_comp_timeRefl, timeRefl_timeRefl]

/-- H2, Proposition 4(c), advanced: `supp G⁻ h ⊆ J⁻(K)` when `supp h ⊆ J⁻(K)`. -/
theorem tsupport_kirchhoffPast_subset {h : Point → ℝ} (hh : Continuous h) {K : Set Point}
    (hK : IsCompact K) (hs : tsupport h ⊆ Jminus K) :
    tsupport (kirchhoff coneMeasurePast h) ⊆ Jminus K := by
  refine closure_minimal (fun p hp => ?_) (isClosed_Jminus hK)
  by_contra hn
  apply hp
  have h0 : kirchhoff coneMeasurePast h p = kirchhoff coneMeasurePast (fun _ => (0 : ℝ)) p := by
    refine kirchhoffPast_congr_of_eqOn hh continuous_const fun q hq => ?_
    by_contra hne
    obtain ⟨k, hk, hqk⟩ := hs (subset_tsupport _ hne)
    obtain ⟨_, rfl, hpq⟩ := hq
    exact hn ⟨k, hk, causalLE_trans hpq hqk⟩
  rw [h0, kirchhoff_apply]
  simp

/-- H2, Proposition 4(d), advanced: `□ G⁻ h = h` and `G⁻ □ h = h`. -/
theorem wave_kirchhoffPast_of_pastSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : PastSupported h) : wave (kirchhoff coneMeasurePast h) = h := by
  have hR := hh.comp contDiff_timeRefl
  rw [kirchhoffPast_eq_comp hh.continuous,
    wave_comp_timeRefl (contDiff_kirchhoff_of_futureSupported hR hs.comp_timeRefl),
    wave_kirchhoff_of_futureSupported hR hs.comp_timeRefl]
  funext p
  simp

/-- The advanced counterpart of `kirchhoff_wave_of_futureSupported`. -/
theorem kirchhoffPast_wave_of_pastSupported {h : Point → ℝ} (hh : ContDiff ℝ ∞ h)
    (hs : PastSupported h) : kirchhoff coneMeasurePast (wave h) = h := by
  have hR := hh.comp contDiff_timeRefl
  rw [kirchhoffPast_eq_comp (contDiff_wave hh).continuous, ← wave_comp_timeRefl hh,
    kirchhoff_wave_of_futureSupported hR hs.comp_timeRefl]
  funext p
  simp

/-! ### Lemma 5: the power bound -/

/-- H2, Lemma 5: if `h` vanishes before `t₀` and `|h| ≤ C (q⁰ − t₀)ⁿ/n!` for `t₀ ≤ q⁰ ≤ T`, then
`|G⁺ h (p)| ≤ C (p⁰ − t₀)ⁿ⁺²/(n + 2)!` for `t₀ ≤ p⁰ ≤ T`. -/
theorem abs_kirchhoff_le {h : Point → ℝ} (hh : Continuous h) {C t₀ T : ℝ} (n : ℕ)
    (h0 : ∀ q : Point, q.1 < t₀ → h q = 0)
    (hC : ∀ q : Point, t₀ ≤ q.1 → q.1 ≤ T → |h q| ≤ C * (q.1 - t₀) ^ n / n.factorial)
    {p : Point} (hp : p.1 ≤ T) (hp0 : t₀ ≤ p.1) :
    |kirchhoff coneMeasure h p| ≤ C * (p.1 - t₀) ^ (n + 2) / (n + 2).factorial := by
  set τ := p.1 - t₀ with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
  -- the radial majorant
  set g : ℝ → ℝ := fun ρ => (Iic τ).indicator (fun ρ => C * (τ - ρ) ^ n / n.factorial * ρ⁻¹) ρ
    with hg
  have hbound : ∀ y : Space, ‖h (p.1 - ‖y‖, p.2 - y) / ‖y‖‖ ≤ g ‖y‖ := by
    intro y
    by_cases hy : ‖y‖ ≤ τ
    · simp only [hg]
      rw [indicator_of_mem (show ‖y‖ ∈ Iic τ from hy), norm_div, Real.norm_eq_abs,
        norm_norm, div_eq_mul_inv]
      have hq := hC (p.1 - ‖y‖, p.2 - y) (by simp only; linarith) (by
        simp only; linarith [norm_nonneg y])
      have e : p.1 - ‖y‖ - t₀ = τ - ‖y‖ := by rw [hτ]; ring
      simp only [e] at hq
      exact mul_le_mul_of_nonneg_right hq (inv_nonneg.2 (norm_nonneg _))
    · simp only [hg]
      rw [indicator_of_notMem (show ‖y‖ ∉ Iic τ from hy),
        h0 _ (by simp only; push Not at hy; linarith)]
      simp
  -- the case `p⁰ = t₀`, and then `p⁰ > t₀`
  rcases eq_or_lt_of_le hτ0 with hτe | hτp
  · -- `p⁰ = t₀`: every sample point lies before `t₀`, up to the null point `y = 0`
    have hz : kirchhoff coneMeasure h p = 0 := by
      rw [kirchhoff_coneMeasure_apply hh]
      have : (fun y : Space => h (p.1 - ‖y‖, p.2 - y) / ‖y‖) = fun _ => 0 := by
        funext y
        by_cases hy : y = 0
        · simp [hy]
        · rw [h0 _ (by simp only; have := norm_pos_iff.2 hy; linarith), zero_div]
      rw [this]
      simp
    rw [hz, ← hτe]
    simp
  -- integrability of the majorant, through the radial formula
  have hg2 : ∀ ρ ∈ Ioi (0 : ℝ), ρ ^ 2 * g ρ =
      (Iic τ).indicator (fun ρ => C / n.factorial * (ρ * (τ - ρ) ^ n)) ρ := by
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := ne_of_gt hρ
    by_cases h' : ρ ≤ τ
    · simp only [hg]
      rw [indicator_of_mem (show ρ ∈ Iic τ from h'), indicator_of_mem (show ρ ∈ Iic τ from h')]
      field_simp
    · simp only [hg]
      rw [indicator_of_notMem (show ρ ∉ Iic τ from h'),
        indicator_of_notMem (show ρ ∉ Iic τ from h')]
      simp
  have hcont : Continuous fun ρ : ℝ => C / n.factorial * (ρ * (τ - ρ) ^ n) := by fun_prop
  have hIoc : IntegrableOn (fun ρ : ℝ => C / n.factorial * (ρ * (τ - ρ) ^ n)) (Ioc 0 τ) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint2 : IntegrableOn (fun ρ : ℝ => ρ ^ 2 * g ρ) (Ioi 0) := by
    refine IntegrableOn.congr_fun ?_ (fun ρ hρ => (hg2 ρ hρ).symm) measurableSet_Ioi
    rw [← integrable_indicator_iff measurableSet_Ioi]
    have e : (Ioi (0 : ℝ)).indicator ((Iic τ).indicator
        (fun ρ : ℝ => C / n.factorial * (ρ * (τ - ρ) ^ n))) =
        (Ioc 0 τ).indicator (fun ρ : ℝ => C / n.factorial * (ρ * (τ - ρ) ^ n)) := by
      rw [indicator_indicator, Ioi_inter_Iic]
    rw [e, integrable_indicator_iff measurableSet_Ioc]
    exact hIoc
  have hintg : Integrable fun y : Space => g ‖y‖ := by
    rw [integrable_fun_norm_addHaar (μ := (volume : Measure Space)) (f := g),
      finrank_euclideanSpace, Fintype.card_fin]
    simpa [smul_eq_mul] using hint2
  -- the estimate
  have hval : ∫ y : Space, g ‖y‖ = 4 * Real.pi * (C / n.factorial *
      (τ ^ (n + 2) / ((n + 1) * (n + 2)))) := by
    rw [integral_radial g, setIntegral_congr_fun measurableSet_Ioi hg2,
      integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi, ← intervalIntegral.integral_of_le hτ0,
      intervalIntegral.integral_const_mul, integral_mul_sub_pow]
  rw [kirchhoff_coneMeasure_apply hh, abs_mul]
  calc |1 / (4 * Real.pi)| * |∫ y : Space, h (p.1 - ‖y‖, p.2 - y) / ‖y‖|
      ≤ |1 / (4 * Real.pi)| * ∫ y : Space, g ‖y‖ := by
        gcongr
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hintg (Eventually.of_forall hbound)
    _ = C * τ ^ (n + 2) / (n + 2).factorial := by
        rw [hval, abs_of_pos (by positivity), Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        field_simp
        ring

/-! ### Corollary 6: iterates -/

/-- Iterates `(G⁺)^k`. -/
noncomputable def kpow (μ : Measure Point) : ℕ → (Point → ℝ) → Point → ℝ
  | 0, f => f
  | k + 1, f => kirchhoff μ (kpow μ k f)

@[simp] theorem kpow_zero (μ : Measure Point) (f : Point → ℝ) : kpow μ 0 f = f := rfl

theorem kpow_succ (μ : Measure Point) (k : ℕ) (f : Point → ℝ) :
    kpow μ (k + 1) f = kirchhoff μ (kpow μ k f) := rfl

/-- `G⁺ h` vanishes before `t₀` when `h` does. -/
theorem kirchhoff_eq_zero_of_lt {h : Point → ℝ} (hh : Continuous h) {t₀ : ℝ}
    (h0 : ∀ q : Point, q.1 < t₀ → h q = 0) {p : Point} (hp : p.1 < t₀) :
    kirchhoff coneMeasure h p = 0 := by
  have := kirchhoff_congr_of_eqOn hh continuous_const (p := p) fun q hq => by
    obtain ⟨r, hr, hqp⟩ := hq
    rw [mem_singleton_iff.1 hr] at hqp
    have : q.1 ≤ p.1 := by
      have := norm_nonneg (p.2 - q.2)
      unfold causalLE at hqp
      linarith
    exact h0 q (by linarith)
  rw [this, kirchhoff_apply]
  simp

/-- H2, Corollary 6(a): the iterates of a smooth future-supported function are smooth,
future-supported (with the same `K`), and vanish before `t₀` when it does. -/
private theorem kpow_contDiff_and_tsupport {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) {K : Set Point}
    (hK : IsCompact K) (hs : tsupport h ⊆ Jplus K) (k : ℕ) :
    ContDiff ℝ ∞ (kpow coneMeasure k h) ∧ tsupport (kpow coneMeasure k h) ⊆ Jplus K := by
  induction k with
  | zero => exact ⟨hh, hs⟩
  | succ k ih =>
    exact ⟨contDiff_kirchhoff_of_futureSupported ih.1 ⟨K, hK, ih.2⟩,
      tsupport_kirchhoff_subset ih.1.continuous hK ih.2⟩

/-- H2, Corollary 6: the powers `(G⁺)ᵏ h` of a smooth `h` supported in `J⁺(K)` are smooth. -/
theorem contDiff_kpow {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) {K : Set Point} (hK : IsCompact K)
    (hs : tsupport h ⊆ Jplus K) (k : ℕ) : ContDiff ℝ ∞ (kpow coneMeasure k h) :=
  (kpow_contDiff_and_tsupport hh hK hs k).1

/-- H2, Corollary 6: the powers `(G⁺)ᵏ h` of a smooth `h` supported in `J⁺(K)` are supported in
`J⁺(K)`. -/
theorem tsupport_kpow_subset {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) {K : Set Point}
    (hK : IsCompact K) (hs : tsupport h ⊆ Jplus K) (k : ℕ) :
    tsupport (kpow coneMeasure k h) ⊆ Jplus K :=
  (kpow_contDiff_and_tsupport hh hK hs k).2

theorem kpow_eq_zero_of_lt {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) {K : Set Point}
    (hK : IsCompact K) (hs : tsupport h ⊆ Jplus K) {t₀ : ℝ}
    (h0 : ∀ q : Point, q.1 < t₀ → h q = 0) (k : ℕ) {p : Point} (hp : p.1 < t₀) :
    kpow coneMeasure k h p = 0 := by
  induction k generalizing p with
  | zero => exact h0 p hp
  | succ k ih =>
    exact kirchhoff_eq_zero_of_lt (contDiff_kpow hh hK hs k).continuous
      (fun q hq => ih hq) hp

/-- H2, Corollary 6(b): `|(G⁺)^k h (p)| ≤ C (p⁰ − t₀)^{2k}/(2k)!` for `t₀ ≤ p⁰ ≤ T`. -/
theorem abs_kpow_le {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) {K : Set Point} (hK : IsCompact K)
    (hs : tsupport h ⊆ Jplus K) {C t₀ T : ℝ} (h0 : ∀ q : Point, q.1 < t₀ → h q = 0)
    (hC : ∀ q : Point, q.1 ≤ T → |h q| ≤ C) (k : ℕ) {p : Point} (hp : p.1 ≤ T)
    (hp0 : t₀ ≤ p.1) :
    |kpow coneMeasure k h p| ≤ C * (p.1 - t₀) ^ (2 * k) / (2 * k).factorial := by
  induction k generalizing p with
  | zero => simpa using hC p hp
  | succ k ih =>
    have := abs_kirchhoff_le (h := kpow coneMeasure k h) (contDiff_kpow hh hK hs k).continuous
      (C := C) (T := T) (2 * k) (fun q hq => kpow_eq_zero_of_lt hh hK hs h0 k hq)
      (fun q hq1 hq2 => ih hq2 hq1) hp hp0
    rw [kpow_succ]
    convert this using 3 <;> ring_nf

/-- H2, Corollary 6(c): `∂ᵥ (G⁺)^k h = (G⁺)^k ∂ᵥ h`. -/
theorem dirDeriv_kpow {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) {K : Set Point} (hK : IsCompact K)
    (hs : tsupport h ⊆ Jplus K) (v : Point) (k : ℕ) :
    dirDeriv v (kpow coneMeasure k h) = kpow coneMeasure k (dirDeriv v h) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [kpow_succ, kpow_succ, dirDeriv_kirchhoff_of_futureSupported (contDiff_kpow hh hK hs k)
      ⟨K, hK, (tsupport_kpow_subset hh hK hs k)⟩, ih]

/-- H2, Corollary 6(c): the derivative bound, `|∂ᵥ (G⁺)^k h (p)| ≤ C' (p⁰ − t₀)^{2k}/(2k)!` when
`|∂ᵥ h| ≤ C'` on `{q⁰ ≤ T}`. -/
theorem abs_dirDeriv_kpow_le {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) {K : Set Point}
    (hK : IsCompact K) (hs : tsupport h ⊆ Jplus K) {C' t₀ T : ℝ}
    (h0 : ∀ q : Point, q.1 < t₀ → h q = 0) (v : Point)
    (hC : ∀ q : Point, q.1 ≤ T → |dirDeriv v h q| ≤ C') (k : ℕ) {p : Point} (hp : p.1 ≤ T)
    (hp0 : t₀ ≤ p.1) :
    |dirDeriv v (kpow coneMeasure k h) p| ≤ C' * (p.1 - t₀) ^ (2 * k) / (2 * k).factorial := by
  have hd0 : ∀ q : Point, q.1 < t₀ → dirDeriv v h q = 0 := by
    intro q hq
    have hev : h =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hq] with r hr
      exact h0 r hr
    rw [(dirDeriv_eventuallyEq hev v).eq_of_nhds]
    simp [dirDeriv, lineDeriv]
  rw [dirDeriv_kpow hh hK hs v k]
  exact abs_kpow_le (contDiff_dirDeriv v hh) hK ((tsupport_dirDeriv_subset v h).trans hs) hd0 hC
    k hp hp0

/-- A compactly supported function is supported in the future of a compact set (its support). -/
theorem futureSupported_of_hasCompactSupport {f : Point → ℝ} (hcf : HasCompactSupport f) :
    FutureSupported f :=
  ⟨tsupport f, hcf, fun q hq => ⟨q, hq, causalLE_refl q⟩⟩

/-- A compactly supported function is supported in the past of a compact set (its support). -/
theorem pastSupported_of_hasCompactSupport {f : Point → ℝ} (hcf : HasCompactSupport f) :
    PastSupported f :=
  ⟨tsupport f, hcf, fun q hq => ⟨q, hq, causalLE_refl q⟩⟩

/-- H2, Definition 1: test functions are supported in the future and in the past of a compact
set (their own support). -/
theorem futureSupported_testFun (f : TestFun) : FutureSupported f :=
  futureSupported_of_hasCompactSupport f.hasCompactSupport

theorem pastSupported_testFun (f : TestFun) : PastSupported f :=
  pastSupported_of_hasCompactSupport f.hasCompactSupport

/-! ### Proposition 7: adjointness -/

/-- H2, Proposition 7: for `u` past-supported and `v` future-supported, `∫ u G⁺ v = ∫ (G⁻ u) v`,
both integrands being integrable. -/
theorem integral_mul_kirchhoff_eq {u v : Point → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hus : PastSupported u) (hvs : FutureSupported v) :
    Integrable (fun p => u p * kirchhoff coneMeasure v p) ∧
      Integrable (fun p => kirchhoff coneMeasurePast u p * v p) ∧
      ∫ p, u p * kirchhoff coneMeasure v p = ∫ p, kirchhoff coneMeasurePast u p * v p := by
  obtain ⟨K', hK', hus'⟩ := hus
  obtain ⟨K, hK, hvs'⟩ := hvs
  set A := Jplus K ∩ Jminus K' with hAdef
  have hA : IsCompact A := isCompact_Jplus_inter_Jminus hK hK'
  obtain ⟨ψ, hψ⟩ := exists_cutoff hA
  have hψA : ∀ q ∈ A, ψ q = 1 := fun q hq => hψ q (self_subset_thickening one_pos _ hq)
  have hGv := tsupport_kirchhoff_subset hv.continuous hK hvs'
  have hGu := tsupport_kirchhoffPast_subset hu.continuous hK' hus'
  set w : TestFun := cutoffTest ψ hv
  set z : TestFun := cutoffTest ψ hu
  -- `G⁺ v = G⁺ (ψ v)` on `A`, and `G⁻ u = G⁻ (ψ u)` on `A`
  have hvA : ∀ p ∈ A, kirchhoff coneMeasure v p = kirchhoff coneMeasure w p := by
    intro p hp
    refine kirchhoff_congr_of_eqOn hv.continuous w.continuous fun q hq => ?_
    by_cases hqs : q ∈ tsupport v
    · obtain ⟨_, rfl, hqp⟩ := hq
      obtain ⟨k', hk', hpk'⟩ := hp.2
      have : q ∈ A := ⟨hvs' hqs, k', hk', causalLE_trans hqp hpk'⟩
      simp [w, hψA q this]
    · have := image_eq_zero_of_notMem_tsupport hqs
      simp [w, this]
  have huA : ∀ p ∈ A, kirchhoff coneMeasurePast u p = kirchhoff coneMeasurePast z p := by
    intro p hp
    refine kirchhoffPast_congr_of_eqOn hu.continuous z.continuous fun q hq => ?_
    by_cases hqs : q ∈ tsupport u
    · obtain ⟨_, rfl, hpq⟩ := hq
      obtain ⟨k, hk, hkp⟩ := hp.1
      have : q ∈ A := ⟨⟨k, hk, causalLE_trans hkp hpq⟩, hus' hqs⟩
      simp [z, hψA q this]
    · have := image_eq_zero_of_notMem_tsupport hqs
      simp [z, this]
  have hGw := tsupport_kirchhoff_subset w.continuous hK
    ((tsupport_mul_subset_right (f := (ψ : Point → ℝ)) (g := v)).trans hvs')
  have hGz := tsupport_kirchhoffPast_subset z.continuous hK'
    ((tsupport_mul_subset_right (f := (ψ : Point → ℝ)) (g := u)).trans hus')
  -- the products agree everywhere with the cut-off ones
  have e1 : ∀ p, u p * kirchhoff coneMeasure v p = z p * kirchhoff coneMeasure w p := by
    intro p
    by_cases hp : p ∈ A
    · simp [z, hψA p hp, hvA p hp]
    · have hl : u p * kirchhoff coneMeasure v p = 0 := by
        by_contra hne
        exact hp ⟨hGv (subset_tsupport _ (right_ne_zero_of_mul hne)),
          hus' (subset_tsupport _ (left_ne_zero_of_mul hne))⟩
      have hr : z p * kirchhoff coneMeasure w p = 0 := by
        by_contra hne
        exact hp ⟨hGw (subset_tsupport _ (right_ne_zero_of_mul hne)),
          hus' (tsupport_mul_subset_right (subset_tsupport _ (left_ne_zero_of_mul hne)))⟩
      rw [hl, hr]
  have e2 : ∀ p, kirchhoff coneMeasurePast u p * v p =
      kirchhoff coneMeasurePast z p * w p := by
    intro p
    by_cases hp : p ∈ A
    · simp [w, hψA p hp, huA p hp]
    · have hl : kirchhoff coneMeasurePast u p * v p = 0 := by
        by_contra hne
        exact hp ⟨hvs' (subset_tsupport _ (right_ne_zero_of_mul hne)),
          hGu (subset_tsupport _ (left_ne_zero_of_mul hne))⟩
      have hr : kirchhoff coneMeasurePast z p * w p = 0 := by
        by_contra hne
        exact hp ⟨hvs' (tsupport_mul_subset_right (subset_tsupport _ (right_ne_zero_of_mul hne))),
          hGz (subset_tsupport _ (left_ne_zero_of_mul hne))⟩
      rw [hl, hr]
  have hint1 : Integrable fun p => z p * kirchhoff coneMeasure w p :=
    (z.continuous.mul (contDiff_kirchhoff coneMeasure w.contDiff
      w.hasCompactSupport).continuous).integrable_of_hasCompactSupport z.hasCompactSupport.mul_right
  have hint2 : Integrable fun p => kirchhoff coneMeasurePast z p * w p :=
    ((contDiff_kirchhoff coneMeasurePast z.contDiff z.hasCompactSupport).continuous.mul
      w.continuous).integrable_of_hasCompactSupport w.hasCompactSupport.mul_left
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e1] using hint1
  · simpa only [e2] using hint2
  · simp_rw [e1, e2]
    have := pairing_gret z w
    rw [pairing_apply, pairing_apply] at this
    simpa [mul_comm] using this

end LinearAQFT.Minkowski
