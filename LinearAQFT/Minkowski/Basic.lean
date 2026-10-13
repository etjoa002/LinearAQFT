/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Analysis.LineDeriv
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Minkowski space, test functions and the wave operator

Stage G, milestone G1. Points of `3+1` Minkowski space `ℝ × ℝ³` with the causal order; test
functions `C_c^∞` (Mathlib's `TestFunction` on the whole space) and smooth functions `C^∞`, with
closed supports (amended 29 Sep 2026; open supports before); the wave operator
`□ = ∂₀² − ∑ᵢ ∂ᵢ²` by line derivatives; and the pairing
`⟨f, h⟩ = ∫ f h`, local, nondegenerate, with `□` formally self-adjoint. These supply conditions
(G1)–(G5) of `Green.GreenData`. Local operators (`IsLocal`, H1, Definition 1) and their
integration by parts (`IsLocal.integral_mul_eq`, H1, Lemma 3) are here too; the case of `□`
(`integral_wave_mul_eq`, G1, Corollary 11) is in `Cutoff.lean`, after the locality of `□`.

**Sign convention.** In the docstrings of `LinearAQFT.Minkowski`, `□` denotes the operator `wave`,
`∂₀² − ∑ᵢ ∂ᵢ²`: the wave operator `P` of the notes. With the mostly-plus signature used
throughout the library this is `−η^{μν}∂_μ∂_ν`, so "□ + μ" below means `P + μ`.

## Main results

* `causalLE_refl`, `causalLE_trans`, `causalLE_antisymm` (G1, Proposition 2).
* `supp_zero`, `supp_add`, `supp_smul` (Lemma 4).
* `contDiff_wave`, `tsupport_wave_subset`, `waveF`, `waveD`, `incl_waveD` (Proposition 6).
* `pairing`, `pairing_eq_zero`, `pairing_nondegenerate` (Propositions 8, 9).
* `pairing_waveD` (Proposition 10).
* `exists_smooth_cutoff`; `IsLocal`, `IsLocal.tsupport_subset`, `IsLocal.integrable_mul`,
  `IsLocal.integral_mul_eq` (H1, Definition 1 and Lemma 3).
-/

namespace LinearAQFT.Minkowski

open scoped Distributions ContDiff Manifold Topology
open TopologicalSpace MeasureTheory Set Filter Function

/-! ### Points and the causal order -/

/-- G1, Definition 1: space `ℝ³`. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- G1, Definition 1: spacetime points `(t, x)`. -/
abbrev Point := ℝ × Space

/-- G1, Definition 1: `q` lies in the closed causal future of `p`. -/
def causalLE (p q : Point) : Prop := ‖q.2 - p.2‖ ≤ q.1 - p.1

/-- G1, Proposition 2. -/
theorem causalLE_refl (p : Point) : causalLE p p := by simp [causalLE]

/-- G1, Proposition 2. -/
theorem causalLE_trans {p q r : Point} (h₁ : causalLE p q) (h₂ : causalLE q r) :
    causalLE p r := by
  unfold causalLE at *
  calc ‖r.2 - p.2‖ = ‖(r.2 - q.2) + (q.2 - p.2)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖r.2 - q.2‖ + ‖q.2 - p.2‖ := norm_add_le _ _
    _ ≤ r.1 - p.1 := by linarith

/-- G1, Proposition 2. -/
theorem causalLE_antisymm {p q : Point} (h₁ : causalLE p q) (h₂ : causalLE q p) : p = q := by
  unfold causalLE at *
  have h0 : q.1 = p.1 := by
    have := norm_nonneg (q.2 - p.2)
    have := norm_nonneg (p.2 - q.2)
    linarith
  have hn : ‖q.2 - p.2‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at hn
  exact Prod.ext h0.symm hn.symm

/-! ### Test functions, functions and supports -/

/-- G1, Definition 3: test functions `C_c^∞(ℝ⁴)`. -/
abbrev TestFun := 𝓓((⊤ : Opens Point), ℝ)

/-- G1, Definition 3: smooth functions `C^∞(ℝ⁴)`. -/
def smooth : Submodule ℝ (Point → ℝ) where
  carrier := {h | ContDiff ℝ ∞ h}
  add_mem' {a b} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) := ha.add hb
  zero_mem' := (contDiff_const : ContDiff ℝ ∞ fun _ : Point => (0 : ℝ))
  smul_mem' c h (hh : ContDiff ℝ ∞ h) := hh.const_smul c

/-- G1, Definition 3: the space `𝓕` of smooth functions. -/
abbrev Fn := smooth

theorem Fn.contDiff (h : Fn) : ContDiff ℝ ∞ (h : Point → ℝ) := h.2

/-- G1, Definition 3 (amended 29 Sep 2026): the support, the closure of `{h ≠ 0}`. -/
def supp (h : Fn) : Set Point := tsupport (h : Point → ℝ)

theorem support_subset_supp (h : Fn) : Function.support (h : Point → ℝ) ⊆ supp h :=
  subset_tsupport _

theorem isClosed_supp (h : Fn) : IsClosed (supp h) := isClosed_tsupport _

/-- G1, Lemma 4. -/
theorem supp_zero : supp 0 = ∅ := by
  simp [supp]

/-- G1, Lemma 4. -/
theorem supp_add (h h' : Fn) : supp (h + h') ⊆ supp h ∪ supp h' := by
  refine closure_minimal (fun p hp => ?_) ((isClosed_supp h).union (isClosed_supp h'))
  by_contra hn
  simp only [mem_union, not_or] at hn
  apply hp
  have h1 : (h : Point → ℝ) p = 0 := by
    by_contra h1
    exact hn.1 (support_subset_supp h h1)
  have h2 : (h' : Point → ℝ) p = 0 := by
    by_contra h2
    exact hn.2 (support_subset_supp h' h2)
  simp [h1, h2]

/-- G1, Lemma 4. -/
theorem supp_smul (c : ℝ) (h : Fn) : supp (c • h) ⊆ supp h := by
  refine closure_minimal (fun p hp => ?_) (isClosed_supp h)
  refine support_subset_supp h fun h0 => hp ?_
  simp [h0]

/-- G1, Definition 3: test functions as functions. -/
noncomputable def incl : TestFun →ₗ[ℝ] Fn where
  toFun f := ⟨f, f.contDiff⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem incl_apply (f : TestFun) (p : Point) : (incl f : Point → ℝ) p = f p := rfl

/-! ### The wave operator -/

/-- The time direction `e₀ = (1, 0)`. -/
def timeDir : Point := (1, 0)

/-- The space directions `eᵢ = (0, δᵢ)`. -/
noncomputable def spaceDir (i : Fin 3) : Point := (0, EuclideanSpace.single i 1)

/-- The derivative in direction `v`, `∂ᵥ h (p) = d/ds h(p + s v)` at `s = 0`. -/
noncomputable def dirDeriv (v : Point) (h : Point → ℝ) : Point → ℝ :=
  fun q => lineDeriv ℝ h q v

theorem dirDeriv_eq_fderiv (v : Point) {h : Point → ℝ} (hh : Differentiable ℝ h) :
    dirDeriv v h = fun q => fderiv ℝ h q v :=
  funext fun q => (hh q).lineDeriv_eq_fderiv

theorem contDiff_dirDeriv (v : Point) {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (dirDeriv v h) :=
  contDiff_lineDeriv hh v

theorem tsupport_dirDeriv_subset (v : Point) (h : Point → ℝ) :
    tsupport (dirDeriv v h) ⊆ tsupport h :=
  tsupport_lineDeriv_subset h v

theorem dirDeriv_add (v : Point) {a b : Point → ℝ} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) : dirDeriv v (a + b) = dirDeriv v a + dirDeriv v b := by
  rw [dirDeriv_eq_fderiv v (ha.add hb), dirDeriv_eq_fderiv v ha, dirDeriv_eq_fderiv v hb]
  funext q
  simp [fderiv_add (ha q) (hb q)]

theorem dirDeriv_smul (v : Point) (c : ℝ) {a : Point → ℝ} (ha : Differentiable ℝ a) :
    dirDeriv v (c • a) = c • dirDeriv v a := by
  rw [dirDeriv_eq_fderiv v (ha.const_smul c), dirDeriv_eq_fderiv v ha]
  funext q
  simp [fderiv_const_smul (ha q)]

/-- G1, Definition 5: the wave operator `□ = ∂₀² − ∑ᵢ ∂ᵢ²`. -/
noncomputable def wave (h : Point → ℝ) : Point → ℝ :=
  dirDeriv timeDir (dirDeriv timeDir h) - ∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) h)

/-- G1, Proposition 6(a). -/
theorem contDiff_wave {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (wave h) := by
  unfold wave
  refine (contDiff_dirDeriv _ (contDiff_dirDeriv _ hh)).sub ?_
  have : (∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) h)) =
      fun p => ∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) h) p := by
    funext p; simp
  rw [this]
  exact ContDiff.sum fun i _ => contDiff_dirDeriv _ (contDiff_dirDeriv _ hh)

/-- G1, Proposition 6(b): `□` does not enlarge closed supports. -/
theorem tsupport_wave_subset (h : Point → ℝ) : tsupport (wave h) ⊆ tsupport h := by
  refine closure_minimal (fun p hp => ?_) (isClosed_tsupport h)
  by_contra hn
  apply hp
  have hz : ∀ v w : Point, dirDeriv w (dirDeriv v h) p = 0 := fun v w =>
    image_eq_zero_of_notMem_tsupport fun hmem =>
      hn (tsupport_dirDeriv_subset v h (tsupport_dirDeriv_subset w _ hmem))
  simp [wave, hz]

theorem wave_add {a b : Point → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    wave (a + b) = wave a + wave b := by
  have d1 : ∀ v, Differentiable ℝ (dirDeriv v a) := fun v =>
    (contDiff_dirDeriv v ha).differentiable (by simp)
  have d2 : ∀ v, Differentiable ℝ (dirDeriv v b) := fun v =>
    (contDiff_dirDeriv v hb).differentiable (by simp)
  have da := ha.differentiable (by simp)
  have db := hb.differentiable (by simp)
  simp only [wave, dirDeriv_add _ da db, dirDeriv_add _ (d1 _) (d2 _), Finset.sum_add_distrib]
  abel

theorem wave_smul (c : ℝ) {a : Point → ℝ} (ha : ContDiff ℝ ∞ a) : wave (c • a) = c • wave a := by
  have d1 : ∀ v, Differentiable ℝ (dirDeriv v a) := fun v =>
    (contDiff_dirDeriv v ha).differentiable (by simp)
  have da := ha.differentiable (by simp)
  simp only [wave, dirDeriv_smul _ c da, dirDeriv_smul _ c (d1 _), ← Finset.smul_sum, smul_sub]

/-- G1, Proposition 6(a): `□` on smooth functions. -/
noncomputable def waveF : Fn →ₗ[ℝ] Fn where
  toFun h := ⟨wave h, contDiff_wave h.2⟩
  map_add' a b := Subtype.ext (wave_add a.2 b.2)
  map_smul' c a := Subtype.ext (wave_smul c a.2)

@[simp] theorem waveF_apply (h : Fn) : (waveF h : Point → ℝ) = wave h := rfl

/-- `□ f` of a test function is a test function. -/
noncomputable def waveDFun (f : TestFun) : TestFun :=
  ⟨wave f, contDiff_wave f.contDiff,
    f.hasCompactSupport.mono' ((subset_tsupport _).trans (tsupport_wave_subset f)),
    by simp⟩

/-- G1, Proposition 6(b): `□` on test functions, `P_𝒟`. -/
noncomputable def waveD : TestFun →ₗ[ℝ] TestFun where
  toFun := waveDFun
  map_add' f g := TestFunction.ext fun p =>
    congrFun (wave_add f.contDiff g.contDiff) p
  map_smul' c f := TestFunction.ext fun p =>
    congrFun (wave_smul c f.contDiff) p

@[simp] theorem waveD_apply (f : TestFun) : (waveD f : Point → ℝ) = wave f := rfl

/-- G1, Proposition 6(b): `ι P_𝒟 = □ ι`. -/
theorem incl_waveD (f : TestFun) : incl (waveD f) = waveF (incl f) := rfl

/-! ### The pairing -/

theorem integrable_mul (f : TestFun) {h : Point → ℝ} (hh : Continuous h) :
    Integrable (fun p => f p * h p) :=
  (f.continuous.mul hh).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right

/-- G1, Definition 7: `⟨f, h⟩ = ∫ f h`. -/
noncomputable def pairing : TestFun →ₗ[ℝ] Fn →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f h => ∫ p, f p * (h : Point → ℝ) p)
    (fun f₁ f₂ h => by
      have e : ∀ p, (f₁ + f₂) p = f₁ p + f₂ p := fun _ => rfl
      simp only [e, add_mul]
      exact integral_add (integrable_mul f₁ (Fn.contDiff h).continuous)
        (integrable_mul f₂ (Fn.contDiff h).continuous))
    (fun c f h => by
      have e : ∀ p, (c • f) p = c * f p := fun _ => rfl
      simp only [e, mul_assoc]
      exact integral_const_mul c _)
    (fun f h₁ h₂ => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_mul f (Fn.contDiff h₁).continuous)
        (integrable_mul f (Fn.contDiff h₂).continuous))
    (fun c f h => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact integral_const_mul c _)

theorem pairing_apply (f : TestFun) (h : Fn) :
    pairing f h = ∫ p, f p * (h : Point → ℝ) p := rfl

/-- G1, Proposition 8: the pairing is local. -/
theorem pairing_eq_zero (f : TestFun) (h : Fn) (hd : Disjoint (supp (incl f)) (supp h)) :
    pairing f h = 0 := by
  rw [pairing_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun p => ?_)
  by_cases hf : f p = 0
  · simp [hf]
  · have hh : (h : Point → ℝ) p = 0 := by
      by_contra hne
      exact Set.disjoint_left.1 hd (support_subset_supp (incl f) hf) (support_subset_supp h hne)
    simp [hh]

/-- G1, Proposition 9: the pairing is nondegenerate in the function. -/
theorem pairing_nondegenerate (h : Fn) (hz : ∀ f, pairing f h = 0) : h = 0 := by
  have hae : ∀ᵐ p ∂(volume : Measure Point), (h : Point → ℝ) p = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (Fn.contDiff h).continuous.locallyIntegrable
      fun g hg hgc => ?_
    have := hz ⟨g, hg, hgc, by simp⟩
    rw [pairing_apply] at this
    simpa [smul_eq_mul] using this
  have hcont : (h : Point → ℝ) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq volume (Fn.contDiff h).continuous continuous_const).1 hae
  exact Subtype.ext hcont

/-! ### Integration by parts -/

instance volume_isAddHaarMeasure : (volume : Measure Point).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem hasCompactSupport_dirDeriv (v : Point) {u : Point → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (dirDeriv v u) :=
  hu.mono' ((subset_tsupport _).trans (tsupport_dirDeriv_subset v u))

theorem integrable_mul_of_or {a b : Point → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : HasCompactSupport a ∨ HasCompactSupport b) : Integrable (fun p => a p * b p) := by
  rcases hc with h | h
  · exact (ha.mul hb).integrable_of_hasCompactSupport h.mul_right
  · exact (ha.mul hb).integrable_of_hasCompactSupport h.mul_left

/-- Integration by parts along a direction, one factor compactly supported. -/
theorem integral_dirDeriv_mul (v : Point) {u w : Point → ℝ} (hu : ContDiff ℝ ∞ u)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport u ∨ HasCompactSupport w) :
    ∫ p, dirDeriv v u p * w p = -∫ p, u p * dirDeriv v w p := by
  have hdu := contDiff_dirDeriv v hu
  have hdw := contDiff_dirDeriv v hw
  have this := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (f := u) (f' := dirDeriv v u) (g := w) (g' := dirDeriv v w) (v := v)
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simpa using (integrable_mul_of_or hdu.continuous hw.continuous
      (hc.imp_left (hasCompactSupport_dirDeriv v))))
    (by simpa using (integrable_mul_of_or hu.continuous hdw.continuous
      (hc.imp_right (hasCompactSupport_dirDeriv v))))
    (by simpa using (integrable_mul_of_or hu.continuous hw.continuous hc))
    (fun x _ => ((hu.differentiable (by simp)) x).lineDifferentiableAt.hasLineDerivAt)
    (fun x _ => ((hw.differentiable (by simp)) x).lineDifferentiableAt.hasLineDerivAt)
  simp only [ContinuousLinearMap.mul_apply'] at this
  linarith

theorem integral_dirDeriv2_mul (v : Point) {u w : Point → ℝ} (hu : ContDiff ℝ ∞ u)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport u ∨ HasCompactSupport w) :
    ∫ p, dirDeriv v (dirDeriv v u) p * w p = ∫ p, u p * dirDeriv v (dirDeriv v w) p := by
  rw [integral_dirDeriv_mul v (contDiff_dirDeriv v hu) hw
      (hc.imp_left (hasCompactSupport_dirDeriv v)),
    integral_dirDeriv_mul v hu (contDiff_dirDeriv v hw)
      (hc.imp_right (hasCompactSupport_dirDeriv v)), neg_neg]

/-- `∫ (□u) w = ∫ u □w` when one of the smooth functions `u`, `w` has compact support. -/
theorem integral_wave_mul {u w : Point → ℝ} (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport u ∨ HasCompactSupport w) :
    ∫ p, wave u p * w p = ∫ p, u p * wave w p := by
  have I1 : ∀ v, Integrable (fun p => dirDeriv v (dirDeriv v u) p * w p) := fun v =>
    integrable_mul_of_or (contDiff_dirDeriv v (contDiff_dirDeriv v hu)).continuous hw.continuous
      (hc.imp_left fun h => hasCompactSupport_dirDeriv v (hasCompactSupport_dirDeriv v h))
  have I2 : ∀ v, Integrable (fun p => u p * dirDeriv v (dirDeriv v w) p) := fun v =>
    integrable_mul_of_or hu.continuous (contDiff_dirDeriv v (contDiff_dirDeriv v hw)).continuous
      (hc.imp_right fun h => hasCompactSupport_dirDeriv v (hasCompactSupport_dirDeriv v h))
  have e1 : (fun p => wave u p * w p) = fun p => dirDeriv timeDir (dirDeriv timeDir u) p * w p -
      ∑ i, dirDeriv (spaceDir i) (dirDeriv (spaceDir i) u) p * w p := by
    funext p
    simp [wave, Finset.sum_apply, sub_mul, Finset.sum_mul]
  have e2 : (fun p => u p * wave w p) = fun p => u p * dirDeriv timeDir (dirDeriv timeDir w) p -
      ∑ i, u p * dirDeriv (spaceDir i) (dirDeriv (spaceDir i) w) p := by
    funext p
    simp [wave, Finset.sum_apply, mul_sub, Finset.mul_sum]
  rw [e1, e2, integral_sub (I1 _) (integrable_finsetSum _ fun i _ => I1 _),
    integral_sub (I2 _) (integrable_finsetSum _ fun i _ => I2 _),
    integral_finsetSum _ fun i _ => I1 _, integral_finsetSum _ fun i _ => I2 _,
    integral_dirDeriv2_mul timeDir hu hw hc]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_dirDeriv2_mul _ hu hw hc

/-- G1, Proposition 10: formal self-adjointness, `⟨□f, h⟩ = ⟨f, □h⟩`. -/
theorem pairing_waveD (f : TestFun) (h : Fn) : pairing (waveD f) h = pairing f (waveF h) :=
  integral_wave_mul f.contDiff (Fn.contDiff h) (Or.inl f.hasCompactSupport)

theorem wave_sub {a b : Point → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    wave (a - b) = wave a - wave b := by
  have hneg : wave (-b) = -wave b := by
    rw [← neg_one_smul ℝ b, wave_smul _ hb, neg_one_smul]
  have hnb : ContDiff ℝ ∞ (-b) := hb.neg
  rw [sub_eq_add_neg, wave_add ha hnb, hneg, ← sub_eq_add_neg]

/-- A smooth, compactly supported function equal to `1` on the `1`-thickening of a compact set. -/
theorem exists_smooth_cutoff {A : Set Point} (hA : IsCompact A) :
    ∃ ψ : Point → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ q ∈ Metric.thickening 1 A, ψ q = 1 := by
  obtain ⟨ψ, hψ, -, hsupp, hone⟩ := exists_contMDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    𝓘(ℝ, Point) (Metric.isOpen_thickening (δ := 2) (E := A)) Metric.isClosed_cthickening
    (Metric.cthickening_subset_thickening' two_pos one_lt_two A)
  refine ⟨ψ, contMDiff_iff_contDiff.1 hψ, ?_, fun q hq =>
    (hone q).1 (Metric.thickening_subset_cthickening _ _ hq)⟩
  refine (hA.cthickening (r := 2)).of_isClosed_subset isClosed_closure ?_
  rw [tsupport, hsupp]
  exact Metric.closure_thickening_subset_cthickening 2 A

section Local

open MeasureTheory Set Filter Function

/-! ### Definition 1 -/

/-- H1, Definition 1: `P` is local if `(P h)(p)` depends only on `h` near `p`. -/
def IsLocal (P : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ (h h' : Fn) (p : Point), (h : Point → ℝ) =ᶠ[𝓝 p] h' →
    (P h : Point → ℝ) p = (P h' : Point → ℝ) p

/-! ### Lemma 3: supports and integration by parts -/

namespace IsLocal

variable {P : Fn →ₗ[ℝ] Fn} (hP : IsLocal P)
include hP

theorem apply_eq_zero {h : Fn} {p : Point} (hp : (h : Point → ℝ) =ᶠ[𝓝 p] 0) :
    (P h : Point → ℝ) p = 0 := by
  have := hP h 0 p (by simpa using hp)
  simpa using this

/-- If `h` vanishes on an open set `W`, then `P h` vanishes on its closure. -/
theorem apply_eq_zero_of_mem_closure {h : Fn} {W : Set Point} (hW : IsOpen W)
    (h0 : ∀ r ∈ W, (h : Point → ℝ) r = 0) {q : Point} (hq : q ∈ closure W) :
    (P h : Point → ℝ) q = 0 := by
  have hW0 : EqOn (P h : Point → ℝ) 0 W := fun r hr =>
    hP.apply_eq_zero (Filter.eventuallyEq_of_mem (hW.mem_nhds hr) h0)
  exact hW0.closure (Fn.contDiff (P h)).continuous continuous_const hq

/-- H1, Lemma 3: a local operator does not enlarge supports. -/
theorem tsupport_subset (h : Fn) : tsupport (P h : Point → ℝ) ⊆ tsupport (h : Point → ℝ) := by
  refine closure_minimal (fun q hq => ?_) (isClosed_tsupport _)
  by_contra hn
  exact hq (hP.apply_eq_zero (notMem_tsupport_iff_eventuallyEq.1 hn))

theorem supp_subset (h : Fn) : supp (P h) ⊆ supp h := hP.tsupport_subset h

/-- H1, Lemma 3: when the supports meet in a compact set, both integrands are integrable. -/
theorem integrable_mul {u v : Fn}
    (hK : IsCompact (tsupport (u : Point → ℝ) ∩ tsupport (v : Point → ℝ))) :
    Integrable (fun p => (P u : Point → ℝ) p * (v : Point → ℝ) p) ∧
      Integrable (fun p => (u : Point → ℝ) p * (P v : Point → ℝ) p) := by
  constructor
  · refine ((Fn.contDiff (P u)).continuous.mul (Fn.contDiff v).continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun p hp => ?_)
    by_contra hne
    exact hp ⟨hP.tsupport_subset u (subset_tsupport _ (left_ne_zero_of_mul hne)),
      subset_tsupport _ (right_ne_zero_of_mul hne)⟩
  · refine ((Fn.contDiff u).continuous.mul (Fn.contDiff (P v)).continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun p hp => ?_)
    by_contra hne
    exact hp ⟨subset_tsupport _ (left_ne_zero_of_mul hne),
      hP.tsupport_subset v (subset_tsupport _ (right_ne_zero_of_mul hne))⟩

/-- H1, Lemma 3: integration by parts for a local, formally self-adjoint operator, when the
supports meet in a compact set. -/
theorem integral_mul_eq {Ptest : TestFun →ₗ[ℝ] TestFun}
    (hi : ∀ f, incl (Ptest f) = P (incl f))
    (hpair : ∀ f h, pairing (Ptest f) h = pairing f (P h)) {u v : Fn}
    (hK : IsCompact (tsupport (u : Point → ℝ) ∩ tsupport (v : Point → ℝ))) :
    ∫ p, (P u : Point → ℝ) p * (v : Point → ℝ) p =
      ∫ p, (u : Point → ℝ) p * (P v : Point → ℝ) p := by
  set K := tsupport (u : Point → ℝ) ∩ tsupport (v : Point → ℝ) with hKdef
  obtain ⟨ψ, hψs, hψc, hone⟩ := exists_smooth_cutoff hK
  set w : TestFun := ⟨fun p => ψ p * (u : Point → ℝ) p, hψs.mul (Fn.contDiff u),
    hψc.mul_right, by simp⟩ with hwdef
  have hw : ∀ p, (incl w : Point → ℝ) p = ψ p * (u : Point → ℝ) p := fun _ => rfl
  have hwu : tsupport (incl w : Point → ℝ) ⊆ tsupport (u : Point → ℝ) := by
    have : (incl w : Point → ℝ) = ψ * (u : Point → ℝ) := funext hw
    rw [this]
    exact tsupport_mul_subset_right
  have hK1 : K ⊆ Metric.thickening 1 K := Metric.self_subset_thickening one_pos K
  have hψ1 : ∀ p ∈ Metric.thickening 1 K, ψ p = 1 := hone
  -- `P u · v = P w · v` pointwise
  have h1 : ∀ p, (P u : Point → ℝ) p * (v : Point → ℝ) p =
      (P (incl w) : Point → ℝ) p * (v : Point → ℝ) p := by
    intro p
    by_cases hvp : (v : Point → ℝ) p = 0
    · simp [hvp]
    by_cases hpU : p ∈ Metric.thickening 1 K
    · have hloc : (incl w : Point → ℝ) =ᶠ[𝓝 p] (u : Point → ℝ) := by
        filter_upwards [Metric.isOpen_thickening.mem_nhds hpU] with r hr
        rw [hw, hψ1 r hr, one_mul]
      rw [hP (incl w) u p hloc]
    · have hpu : p ∉ tsupport (u : Point → ℝ) := fun hpu =>
        hpU (hK1 ⟨hpu, subset_tsupport _ hvp⟩)
      rw [image_eq_zero_of_notMem_tsupport (fun h => hpu (hP.tsupport_subset u h)),
        image_eq_zero_of_notMem_tsupport (fun h => hpu (hwu (hP.tsupport_subset _ h)))]
  -- `w · P v = u · P v` pointwise
  have h2 : ∀ p, (incl w : Point → ℝ) p * (P v : Point → ℝ) p =
      (u : Point → ℝ) p * (P v : Point → ℝ) p := by
    intro p
    by_cases hup : (u : Point → ℝ) p = 0
    · simp [hw, hup]
    by_cases hpU : p ∈ Metric.thickening 1 K
    · rw [hw, hψ1 p hpU, one_mul]
    · have hpv : p ∉ tsupport (v : Point → ℝ) := fun hpv =>
        hpU (hK1 ⟨subset_tsupport _ hup, hpv⟩)
      rw [image_eq_zero_of_notMem_tsupport (fun h => hpv (hP.tsupport_subset v h)),
        mul_zero, mul_zero]
  calc ∫ p, (P u : Point → ℝ) p * (v : Point → ℝ) p
      = ∫ p, (P (incl w) : Point → ℝ) p * (v : Point → ℝ) p := by simp_rw [h1]
    _ = pairing (Ptest w) v := by rw [pairing_apply, ← hi]; rfl
    _ = pairing w (P v) := hpair w v
    _ = ∫ p, (incl w : Point → ℝ) p * (P v : Point → ℝ) p := rfl
    _ = ∫ p, (u : Point → ℝ) p * (P v : Point → ℝ) p := by simp_rw [h2]

end IsLocal

end Local

end LinearAQFT.Minkowski
