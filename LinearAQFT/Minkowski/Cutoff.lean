/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Causal
import LinearAQFT.Analysis.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Time functions, compactness and the inertial-slab cutoffs

Stage G, milestone G4 (Definitions 1 and 4, Lemmas 2 and 3). The Minkowski form `η` (mostly
plus), future unit vectors `n` and their time functions `τₙ(p) = −η(n, p)`; compactness of the
causal future and past `J^±(K)` (defined in `Kirchhoff.lean`) after cutting by a level of `τₙ`;
the cutoffs `(n, t₁, t₂)` with slab `t₁ ≤ τₙ ≤ t₂` and smooth function `χ`; locality of `□`.
Conditions (c1) and (c2) are proved for every local operator in `GreenOps.lean` (stage H,
milestone H1) and specialized to `□` in `GreenData.lean`.

## Main results

* `timeFun_ge` (Lemma 2); `isCompact_Jplus_inter`, `isCompact_Jminus_inter` (Lemma 3).
* `Cutoff`, `chiFun`, `slab`, `isClosed_slab`, `chi` (Definition 4).
* `wave_congr_of_eventuallyEq`, `isLocal_waveF` (locality of `□`); `integral_wave_mul_eq`
  (G1, Corollary 11) and `integrable_wave_mul_of_isCompact`.
* `isCompact_Jplus_inter_Jminus`.
-/
namespace LinearAQFT.Minkowski

open scoped ContDiff InnerProductSpace Topology Pointwise
open MeasureTheory Set Filter Function Metric

/-! ### The Minkowski form and time functions -/

/-- G4, Definition 1: the Minkowski form `η(u, w) = −u⁰w⁰ + u⃗·w⃗`. -/
noncomputable def eta (u w : Point) : ℝ := -(u.1 * w.1) + ⟪u.2, w.2⟫_ℝ

/-- G4, Definition 1: `n` is future unit, `n⁰ > 0` and `η(n, n) = −1`. -/
def IsFutureUnit (n : Point) : Prop := 0 < n.1 ∧ eta n n = -1

/-- G4, Definition 1: the time function `τₙ(p) = −η(n, p)`. -/
noncomputable def timeFun (n p : Point) : ℝ := -eta n p

theorem timeFun_apply (n p : Point) : timeFun n p = n.1 * p.1 - ⟪n.2, p.2⟫_ℝ := by
  simp only [timeFun, eta]
  ring

theorem timeFun_add (n p q : Point) : timeFun n (p + q) = timeFun n p + timeFun n q := by
  simp only [timeFun_apply, Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

theorem timeFun_neg (n p : Point) : timeFun n (-p) = -timeFun n p := by
  simp only [timeFun_apply, Prod.fst_neg, Prod.snd_neg, inner_neg_right]
  ring

theorem timeFun_sub (n p q : Point) : timeFun n (p - q) = timeFun n p - timeFun n q := by
  rw [sub_eq_add_neg, timeFun_add, timeFun_neg, ← sub_eq_add_neg]

theorem contDiff_timeFun (n : Point) : ContDiff ℝ ∞ (timeFun n) := by
  have e : timeFun n = fun p : Point => n.1 * p.1 - ⟪n.2, p.2⟫_ℝ := funext (timeFun_apply n)
  rw [e]
  exact (contDiff_const.mul contDiff_fst).sub (contDiff_const.inner ℝ contDiff_snd)

theorem continuous_timeFun (n : Point) : Continuous (timeFun n) :=
  (contDiff_timeFun n).continuous

theorem IsFutureUnit.norm_lt {n : Point} (hn : IsFutureUnit n) : ‖n.2‖ < n.1 := by
  have h := hn.2
  simp only [eta, real_inner_self_eq_norm_sq] at h
  nlinarith [hn.1, norm_nonneg n.2]

/-- G4, Lemma 2: `τₙ(v) ≥ (n⁰ − |n⃗|) v⁰` for future causal `v`. -/
theorem timeFun_ge {n v : Point} (hv : ‖v.2‖ ≤ v.1) :
    (n.1 - ‖n.2‖) * v.1 ≤ timeFun n v := by
  rw [timeFun_apply]
  nlinarith [real_inner_le_norm n.2 v.2, norm_nonneg n.2,
    mul_le_mul_of_nonneg_left hv (norm_nonneg n.2)]

/-- G4, Lemma 2: `τₙ(v) ≥ 0` for `n` future unit and `v` future causal. -/
theorem timeFun_nonneg {n v : Point} (hn : IsFutureUnit n) (hv : ‖v.2‖ ≤ v.1) :
    0 ≤ timeFun n v := by
  have h := timeFun_ge (n := n) hv
  have hd : 0 ≤ n.1 - ‖n.2‖ := (sub_pos.2 hn.norm_lt).le
  nlinarith [(norm_nonneg v.2).trans hv]

/-- The time direction is future unit. -/
theorem isFutureUnit_timeDir : IsFutureUnit timeDir := by
  refine ⟨by simp [timeDir], ?_⟩
  simp [eta, timeDir]

theorem timeFun_timeDir (p : Point) : timeFun timeDir p = p.1 := by
  simp [timeFun_apply, timeDir]

/-- G4, Lemma 3: `J⁺(K) ∩ {τₙ ≤ T}` is compact. -/
theorem isCompact_Jplus_inter {K : Set Point} (hK : IsCompact K) {n : Point}
    (hn : IsFutureUnit n) (T : ℝ) : IsCompact (Jplus K ∩ {p | timeFun n p ≤ T}) := by
  refine isCompact_of_isClosed_isBounded
    ((isClosed_Jplus hK).inter (isClosed_le (continuous_timeFun n) continuous_const)) ?_
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨m, hm⟩ := hK.bddBelow_image (continuous_timeFun n).continuousOn
  have hd : 0 < n.1 - ‖n.2‖ := sub_pos.2 hn.norm_lt
  set B := (T - m) / (n.1 - ‖n.2‖)
  refine (isBounded_closedBall (x := (0 : Point)) (r := R + B)).subset ?_
  rintro q ⟨⟨p, hp, hpq⟩, hq⟩
  have hpR := hR hp
  rw [mem_closedBall_zero_iff] at hpR ⊢
  set v := q - p
  have hv : ‖v.2‖ ≤ v.1 := by simpa [v, causalLE] using hpq
  have hτ : timeFun n v ≤ T - m := by
    rw [timeFun_sub]
    have := hm ⟨p, hp, rfl⟩
    simp only [Set.mem_ofPred_eq] at hq
    linarith
  have hv1 : v.1 ≤ B := by
    rw [le_div_iff₀ hd]
    nlinarith [timeFun_ge (n := n) hv]
  have hvB : ‖v‖ ≤ B := by
    rw [norm_prod_le_iff]
    refine ⟨?_, hv.trans hv1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg ((norm_nonneg _).trans hv)]
    exact hv1
  calc ‖q‖ = ‖p + v‖ := by rw [add_sub_cancel]
    _ ≤ ‖p‖ + ‖v‖ := norm_add_le _ _
    _ ≤ R + B := add_le_add hpR hvB

/-- G4, Lemma 3: `J⁻(K) ∩ {τₙ ≥ T}` is compact. -/
theorem isCompact_Jminus_inter {K : Set Point} (hK : IsCompact K) {n : Point}
    (hn : IsFutureUnit n) (T : ℝ) : IsCompact (Jminus K ∩ {p | T ≤ timeFun n p}) := by
  have e : Jminus K ∩ {p | T ≤ timeFun n p} = -(Jplus (-K) ∩ {p | timeFun n p ≤ -T}) := by
    ext q
    rw [Jminus_eq_neg]
    simp only [Set.mem_neg, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : T ≤ timeFun n q := h2
      refine ⟨h1, ?_⟩
      change timeFun n (-q) ≤ -T
      rw [timeFun_neg]
      linarith
    · rintro ⟨h1, h2⟩
      have h2' : timeFun n (-q) ≤ -T := h2
      rw [timeFun_neg] at h2'
      exact ⟨h1, show T ≤ timeFun n q by linarith⟩
  rw [e]
  exact (isCompact_Jplus_inter hK.neg hn (-T)).neg

/-! ### Cutoffs -/

/-- G4, Definition 4: a cutoff `(n, t₁, t₂)`, `n` future unit and `t₁ < t₂`. -/
@[ext]
structure Cutoff : Type where
  n : Point
  hn : IsFutureUnit n
  t₁ : ℝ
  t₂ : ℝ
  lt : t₁ < t₂

/-- G4, Definition 4: `χ(p) = σ((τₙ(p) − t₁)/(t₂ − t₁))`, `σ` the smooth transition. -/
noncomputable def chiFun (c : Cutoff) (p : Point) : ℝ :=
  Real.smoothTransition ((timeFun c.n p - c.t₁) / (c.t₂ - c.t₁))

/-- G4, Definition 4: the slab `t₁ ≤ τₙ ≤ t₂`. -/
def slab (c : Cutoff) : Set Point := {p | c.t₁ ≤ timeFun c.n p ∧ timeFun c.n p ≤ c.t₂}

theorem contDiff_chiFun (c : Cutoff) : ContDiff ℝ ∞ (chiFun c) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    (((contDiff_timeFun c.n).sub contDiff_const).div_const _)

theorem chiFun_eq_zero (c : Cutoff) {p : Point} (h : timeFun c.n p ≤ c.t₁) : chiFun c p = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) (sub_pos.2 c.lt).le)

theorem chiFun_eq_one (c : Cutoff) {p : Point} (h : c.t₂ ≤ timeFun c.n p) : chiFun c p = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.2 c.lt)).2 (by linarith))

/-- G4, Definition 4: multiplication by `χ` on smooth functions. -/
noncomputable def chi (c : Cutoff) : Fn →ₗ[ℝ] Fn where
  toFun h := ⟨fun p => chiFun c p * (h : Point → ℝ) p, (contDiff_chiFun c).mul (Fn.contDiff h)⟩
  map_add' h h' := Subtype.ext (funext fun p => by simp [mul_add])
  map_smul' a h := Subtype.ext (funext fun p => by simp [mul_left_comm])

@[simp] theorem chi_apply (c : Cutoff) (h : Fn) (p : Point) :
    (chi c h : Point → ℝ) p = chiFun c p * (h : Point → ℝ) p := rfl

/-! ### Locality of `□` -/

theorem dirDeriv_eventuallyEq {h h' : Point → ℝ} {p : Point} (hpq : h =ᶠ[𝓝 p] h') (v : Point) :
    dirDeriv v h =ᶠ[𝓝 p] dirDeriv v h' :=
  hpq.eventuallyEq_nhds.mono fun _ hy => hy.lineDeriv_eq

/-- `□` is local: functions equal near `p` have the same `□` at `p`. -/
theorem wave_congr_of_eventuallyEq {h h' : Point → ℝ} {p : Point} (hpq : h =ᶠ[𝓝 p] h') :
    wave h p = wave h' p := by
  have hdd : ∀ v, dirDeriv v (dirDeriv v h) p = dirDeriv v (dirDeriv v h') p := fun v =>
    (dirDeriv_eventuallyEq hpq v).lineDeriv_eq
  simp only [wave, Pi.sub_apply, Finset.sum_apply, hdd]

/-- H1, Proposition 10: `□` is local. -/
theorem isLocal_waveF : IsLocal waveF := fun _ _ _ hpq => wave_congr_of_eventuallyEq hpq

/-- G1, Corollary 11: `∫ (□u) v = ∫ u □v` for smooth `u`, `v` whose closed supports meet in a
compact set; the case `P = □` of `IsLocal.integral_mul_eq`. -/
theorem integral_wave_mul_eq {u v : Point → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hK : IsCompact (tsupport u ∩ tsupport v)) :
    ∫ p, wave u p * v p = ∫ p, u p * wave v p :=
  isLocal_waveF.integral_mul_eq incl_waveD pairing_waveD (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) hK

/-- The integrands of G1, Corollary 11 are integrable (carried stage-G finding 2); the case
`P = □` of `IsLocal.integrable_mul`. -/
theorem integrable_wave_mul_of_isCompact {u v : Point → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (hK : IsCompact (tsupport u ∩ tsupport v)) :
    Integrable (fun p => wave u p * v p) ∧ Integrable (fun p => u p * wave v p) :=
  isLocal_waveF.integrable_mul (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) hK

/-- `J⁺(K) ∩ J⁻(K')` is compact for compact `K`, `K'`. -/
theorem isCompact_Jplus_inter_Jminus {K K' : Set Point} (hK : IsCompact K) (hK' : IsCompact K') :
    IsCompact (Jplus K ∩ Jminus K') := by
  obtain ⟨T, hT⟩ := hK'.bddAbove_image continuous_fst.continuousOn
  refine (isCompact_Jplus_inter hK isFutureUnit_timeDir T).of_isClosed_subset
    ((isClosed_Jplus hK).inter (isClosed_Jminus hK')) fun q ⟨hq, p, hp, hqp⟩ => ⟨hq, ?_⟩
  change timeFun timeDir q ≤ T
  rw [timeFun_timeDir]
  have h1 := hT ⟨p, hp, rfl⟩
  have h2 : ‖p.2 - q.2‖ ≤ p.1 - q.1 := hqp
  linarith [norm_nonneg (p.2 - q.2)]

theorem isClosed_slab (c : Cutoff) : IsClosed (slab c) :=
  (isClosed_le continuous_const (continuous_timeFun c.n)).inter
    (isClosed_le (continuous_timeFun c.n) continuous_const)

end LinearAQFT.Minkowski
