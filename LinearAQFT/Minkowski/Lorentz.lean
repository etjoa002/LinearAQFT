/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Cutoff
import LinearAQFT.Minkowski.Wave
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Orthochronous Lorentz maps and the Poincaré group

Stage G, milestone G4 (Definition 10, Lemma 11, and the maps of Proposition 12), split from
`Poincare.lean` in stage H (milestone H1) so that the general theory of Green operators
(`GreenOps.lean`) can use it. Orthochronous Lorentz maps preserve the causal order, map future unit
vectors to future unit vectors, have `|det| = 1` and commute with `□`; an orthochronous Poincaré
map acts on points, test functions, smooth functions and cutoffs.

Coordinates of `ℝ⁴` are indexed by `Fin 1 ⊕ Fin 3` (Physlib's convention, for a later bridge);
the Minkowski matrix in this basis is `diag(−1, 1, 1, 1)`.

## Main results

* `LorentzMap`, `Poincare` (Definition 10), with their group structures.
* `LorentzMap.injective_of_eta` (Lemma 11(a)); `Poincare.causalLE_iff` (b);
  `LorentzMap.isFutureUnit_map`, `LorentzMap.timeFun_symm` (c); `LorentzMap.abs_det`,
  `Poincare.measurePreserving` (d); `wave_comp_lorentz`, `Poincare.wave_comp` (e).
* `Poincare.mapCutoff`, `Poincare.pushD`, `Poincare.pushF`, `Poincare.pairing_push`.
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff InnerProductSpace Topology Matrix
open MeasureTheory Set Filter Function

/-! ### The Minkowski form as a bilinear map, and the standard basis -/

theorem eta_symm (u w : Point) : eta u w = eta w u := by
  simp only [eta, real_inner_comm]
  ring

/-- The Minkowski form `η` as a bilinear map. -/
noncomputable def etaBilin : Point →ₗ[ℝ] Point →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ eta
    (fun u u' w => by simp only [eta, Prod.fst_add, Prod.snd_add, inner_add_left]; ring)
    (fun c u w => by simp only [eta, Prod.smul_fst, Prod.smul_snd, inner_smul_left, smul_eq_mul]
                     simp; ring)
    (fun u w w' => by simp only [eta, Prod.fst_add, Prod.snd_add, inner_add_right]; ring)
    (fun c u w => by simp only [eta, Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul]
                     ring)

@[simp] theorem etaBilin_apply (u w : Point) : etaBilin u w = eta u w := rfl

/-- `η` is nondegenerate. -/
theorem eq_zero_of_eta {u : Point} (h : ∀ w, eta u w = 0) : u = 0 := by
  have h1 := h (-u.1, u.2)
  simp only [eta, real_inner_self_eq_norm_sq] at h1
  have h2 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg ‖u.2‖]
  have h3 : ‖u.2‖ = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg ‖u.2‖, norm_nonneg u.2]
  exact Prod.ext h2 (norm_eq_zero.1 h3)

theorem eta_timeDir_left (x : Point) : eta timeDir x = -x.1 := by
  simp [eta, timeDir]

/-- The standard basis `e₀, e₁, e₂, e₃` of `ℝ⁴`, indexed by `Fin 1 ⊕ Fin 3`. -/
noncomputable def stdBasis : Module.Basis (Fin 1 ⊕ Fin 3) ℝ Point :=
  (Module.Basis.singleton (Fin 1) ℝ).prod (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

theorem stdBasis_inl (i : Fin 1) : stdBasis (Sum.inl i) = timeDir := by
  ext
  · simp [stdBasis, timeDir]
  · simp [stdBasis, timeDir]

theorem stdBasis_inr (i : Fin 3) : stdBasis (Sum.inr i) = spaceDir i := by
  ext
  · simp [stdBasis, spaceDir]
  · simp [stdBasis, spaceDir, EuclideanSpace.basisFun_apply]

/-- The signs of the Minkowski matrix `diag(−1, 1, 1, 1)`. -/
def etaSign : Fin 1 ⊕ Fin 3 → ℝ := Sum.elim (fun _ => -1) (fun _ => 1)

/-- The Minkowski matrix is `diag(−1, 1, 1, 1)` in the standard basis. -/
theorem toMatrix2_etaBilin :
    LinearMap.toMatrix₂ stdBasis stdBasis etaBilin = Matrix.diagonal etaSign := by
  ext i j
  rw [LinearMap.toMatrix₂_apply, etaBilin_apply]
  rcases i with i | i <;> rcases j with j | j
  · have : i = j := Subsingleton.elim i j
    subst this
    simp [stdBasis_inl, eta, timeDir, etaSign]
  · simp [stdBasis_inl, stdBasis_inr, eta, timeDir, spaceDir, etaSign]
  · simp [stdBasis_inl, stdBasis_inr, eta, timeDir, spaceDir, etaSign]
  · by_cases h : i = j
    · subst h
      simp [stdBasis_inr, eta, spaceDir, etaSign]
    · simp [stdBasis_inr, eta, spaceDir, etaSign, h, EuclideanSpace.inner_single_left]

theorem etaSign_mul_self (i : Fin 1 ⊕ Fin 3) : etaSign i * etaSign i = 1 := by
  rcases i with i | i <;> simp [etaSign]

theorem diagonal_etaSign_mul_self :
    Matrix.diagonal etaSign * Matrix.diagonal etaSign = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp [etaSign_mul_self]

theorem det_diagonal_etaSign : (Matrix.diagonal etaSign).det = -1 := by
  rw [Matrix.det_diagonal, Fintype.prod_sum_type]
  simp [etaSign]

/-! ### Orthochronous Lorentz maps -/

/-- G4, Definition 10: an orthochronous Lorentz map, `η(Lu, Lw) = η(u, w)` and `(L e₀)⁰ > 0`
(stored as a continuous linear equivalence; invertibility is Lemma 11(a)). -/
@[ext]
structure LorentzMap where
  toEquiv : Point ≃L[ℝ] Point
  eta_map : ∀ u w, eta (toEquiv u) (toEquiv w) = eta u w
  orthochronous : 0 < (toEquiv timeDir).1

/-- G4, Lemma 11(a): a linear map preserving `η` is injective (hence invertible). -/
theorem LorentzMap.injective_of_eta (L : Point →ₗ[ℝ] Point)
    (h : ∀ u w, eta (L u) (L w) = eta u w) : Function.Injective L := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  exact eq_zero_of_eta fun w => by rw [← h, hu]; simp [eta]

/-- G4, Definition 10 and Lemma 11(a): a linear map preserving `η` with `(L e₀)⁰ > 0` is an
orthochronous Lorentz map (it is injective, hence invertible). -/
noncomputable def LorentzMap.ofLinearMap (L : Point →ₗ[ℝ] Point)
    (h : ∀ u w, eta (L u) (L w) = eta u w) (h0 : 0 < (L timeDir).1) : LorentzMap where
  toEquiv :=
    (LinearEquiv.ofInjectiveEndo L (LorentzMap.injective_of_eta L h)).toContinuousLinearEquiv
  eta_map := h
  orthochronous := h0

@[simp] theorem LorentzMap.ofLinearMap_apply (L : Point →ₗ[ℝ] Point)
    (h : ∀ u w, eta (L u) (L w) = eta u w) (h0 : 0 < (L timeDir).1) (x : Point) :
    (LorentzMap.ofLinearMap L h h0).toEquiv x = L x := rfl

namespace LorentzMap

variable (L : LorentzMap)

instance : CoeFun LorentzMap (fun _ => Point → Point) := ⟨fun L => L.toEquiv⟩

theorem eta_symm_map (u w : Point) : eta (L.toEquiv.symm u) (L.toEquiv.symm w) = eta u w := by
  rw [← L.eta_map, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem fst_symm_timeDir : (L.toEquiv.symm timeDir).1 = (L.toEquiv timeDir).1 := by
  have h := L.eta_map (L.toEquiv.symm timeDir) timeDir
  rw [ContinuousLinearEquiv.apply_symm_apply, eta_timeDir_left,
    eta_symm (L.toEquiv.symm timeDir), eta_timeDir_left] at h
  linarith

theorem isFutureUnit_symm_timeDir : IsFutureUnit (L.toEquiv.symm timeDir) :=
  ⟨by rw [fst_symm_timeDir]; exact L.orthochronous,
    by rw [eta_symm_map]; exact isFutureUnit_timeDir.2⟩

/-- `(L v)⁰ = τ_w(v)` with `w = L⁻¹ e₀`. -/
theorem fst_apply (v : Point) : (L.toEquiv v).1 = timeFun (L.toEquiv.symm timeDir) v := by
  rw [timeFun, ← L.eta_map, ContinuousLinearEquiv.apply_symm_apply, eta_timeDir_left, neg_neg]

/-- G4, Lemma 11(b): `L` maps future causal vectors to future causal vectors. -/
theorem futureCausal_map {v : Point} (hv : ‖v.2‖ ≤ v.1) :
    ‖(L.toEquiv v).2‖ ≤ (L.toEquiv v).1 := by
  have hw := L.isFutureUnit_symm_timeDir
  have h0 : 0 ≤ (L.toEquiv v).1 := by
    rw [fst_apply]
    have := timeFun_ge (n := L.toEquiv.symm timeDir) hv
    have hd : 0 ≤ (L.toEquiv.symm timeDir).1 - ‖(L.toEquiv.symm timeDir).2‖ :=
      (sub_pos.2 hw.norm_lt).le
    nlinarith [(norm_nonneg v.2).trans hv]
  have he := L.eta_map v v
  simp only [eta, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (L.toEquiv v).2, norm_nonneg v.2]

/-- G4, Lemma 11(c): `L` maps future unit vectors to future unit vectors. -/
theorem isFutureUnit_map {n : Point} (hn : IsFutureUnit n) : IsFutureUnit (L.toEquiv n) := by
  refine ⟨?_, by rw [L.eta_map]; exact hn.2⟩
  have hw := L.isFutureUnit_symm_timeDir
  rw [fst_apply]
  have := timeFun_ge (n := L.toEquiv.symm timeDir) hn.norm_lt.le
  have hd : 0 < (L.toEquiv.symm timeDir).1 - ‖(L.toEquiv.symm timeDir).2‖ := sub_pos.2 hw.norm_lt
  nlinarith [hn.1]

/-- G4, Lemma 11(c): `τₙ(L⁻¹ x) = τ_{Ln}(x)`. -/
theorem timeFun_symm (n x : Point) : timeFun n (L.toEquiv.symm x) = timeFun (L.toEquiv n) x := by
  rw [timeFun, timeFun, ← L.eta_map, ContinuousLinearEquiv.apply_symm_apply]

/-- The matrix of `L` in the standard basis. -/
noncomputable def matrix : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  LinearMap.toMatrix stdBasis stdBasis (L.toEquiv : Point →ₗ[ℝ] Point)

/-- `Lᵀ η L = η` in the standard basis. -/
theorem matrix_transpose_mul :
    L.matrixᵀ * Matrix.diagonal etaSign * L.matrix = Matrix.diagonal etaSign := by
  rw [← toMatrix2_etaBilin, matrix, ← LinearMap.toMatrix₂_compl₁₂]
  congr 1
  refine LinearMap.ext fun u => LinearMap.ext fun w => ?_
  simp [L.eta_map]

/-- `L η⁻¹ Lᵀ = η⁻¹` (here `η⁻¹ = η`). -/
theorem matrix_mul_transpose :
    L.matrix * Matrix.diagonal etaSign * L.matrixᵀ = Matrix.diagonal etaSign := by
  have h1 : (Matrix.diagonal etaSign * L.matrixᵀ * Matrix.diagonal etaSign) * L.matrix = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc L.matrixᵀ, matrix_transpose_mul,
      diagonal_etaSign_mul_self]
  have h2 := mul_eq_one_comm.1 h1
  calc L.matrix * Matrix.diagonal etaSign * L.matrixᵀ
      = L.matrix * Matrix.diagonal etaSign * L.matrixᵀ *
          (Matrix.diagonal etaSign * Matrix.diagonal etaSign) := by
        rw [diagonal_etaSign_mul_self, Matrix.mul_one]
    _ = (L.matrix * (Matrix.diagonal etaSign * L.matrixᵀ * Matrix.diagonal etaSign)) *
          Matrix.diagonal etaSign := by simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal etaSign := by rw [h2, Matrix.one_mul]

/-- G4, Lemma 11(d): `|det L| = 1`. -/
theorem abs_det : |LinearMap.det (L.toEquiv : Point →ₗ[ℝ] Point)| = 1 := by
  have h := congrArg Matrix.det L.matrix_transpose_mul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_diagonal_etaSign] at h
  have hsq : L.matrix.det * L.matrix.det = 1 := by linarith
  rw [← LinearMap.det_toMatrix stdBasis]
  change |L.matrix.det| = 1
  rcases mul_self_eq_one_iff.1 hsq with h1 | h1 <;> simp [h1]

theorem det_ne_zero : LinearMap.det (L.toEquiv : Point →ₗ[ℝ] Point) ≠ 0 := by
  intro h
  have := L.abs_det
  rw [h, abs_zero] at this
  exact zero_ne_one this

/-- G4, Lemma 11(d): `L` preserves Lebesgue measure. -/
theorem measurePreserving : MeasurePreserving (L.toEquiv : Point → Point) := by
  refine ⟨L.toEquiv.continuous.measurable, ?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure Point))
    L.det_ne_zero
  rw [abs_inv, L.abs_det, inv_one, ENNReal.ofReal_one, one_smul] at h
  exact h

end LorentzMap

/-! ### `□` in matrix form, and its Lorentz invariance -/

/-- The second derivative of `h` at `y` as a bilinear map. -/
noncomputable def hessBilin (h : Point → ℝ) (y : Point) : Point →ₗ[ℝ] Point →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u w => fderiv ℝ (fderiv ℝ h) y u w)
    (fun u u' w => by simp [map_add])
    (fun c u w => by simp [map_smul])
    (fun u w w' => by simp [map_add])
    (fun c u w => by simp [map_smul])

@[simp] theorem hessBilin_apply (h : Point → ℝ) (y u w : Point) :
    hessBilin h y u w = fderiv ℝ (fderiv ℝ h) y u w := rfl

/-- The Hessian matrix in the standard basis. -/
noncomputable def hessMatrix (h : Point → ℝ) (y : Point) :
    Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ :=
  LinearMap.toMatrix₂ stdBasis stdBasis (hessBilin h y)

/-- `□h(y) = −tr(η H(y))`, `H` the Hessian matrix. -/
theorem wave_eq_trace {h : Point → ℝ} (hh : ContDiff ℝ 2 h) (y : Point) :
    wave h y = -(Matrix.diagonal etaSign * hessMatrix h y).trace := by
  have hdd : ∀ v, dirDeriv v (dirDeriv v h) y = fderiv ℝ (fderiv ℝ h) y v v := fun v =>
    lineDeriv_lineDeriv_eq_fderiv hh y v v
  simp only [wave, Pi.sub_apply, Finset.sum_apply, hdd, Matrix.trace, Matrix.diag,
    Matrix.diagonal_mul, hessMatrix, LinearMap.toMatrix₂_apply, hessBilin_apply,
    Fintype.sum_sum_type, Fin.sum_univ_one, stdBasis_inl, stdBasis_inr, etaSign, Sum.elim_inl,
    Sum.elim_inr]
  ring_nf

/-- The chain rule for second derivatives under a continuous linear map. -/
theorem fderiv_fderiv_comp_clm {h : Point → ℝ} (hh : ContDiff ℝ 2 h) (L : Point →L[ℝ] Point)
    (y u w : Point) :
    fderiv ℝ (fderiv ℝ (h ∘ L)) y u w = fderiv ℝ (fderiv ℝ h) (L y) (L u) (L w) := by
  have e1 := iteratedFDeriv_two_apply (𝕜 := ℝ) (h ∘ L) y ![u, w]
  have e2 := iteratedFDeriv_two_apply (𝕜 := ℝ) h (L y) ![L u, L w]
  rw [L.iteratedFDeriv_comp_right hh y le_rfl] at e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2
  rw [← e1, ← e2]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- G4, Lemma 11(e): `□(h ∘ L) = (□h) ∘ L` for an orthochronous Lorentz map `L`. -/
theorem wave_comp_lorentz {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) (L : LorentzMap) :
    wave (h ∘ L.toEquiv) = wave h ∘ L.toEquiv := by
  have hh2 : ContDiff ℝ 2 h := hh.of_le (by norm_cast)
  have hL2 : ContDiff ℝ 2 (h ∘ L.toEquiv) := hh2.comp L.toEquiv.contDiff
  funext y
  have hH : hessMatrix (h ∘ L.toEquiv) y = L.matrixᵀ * hessMatrix h (L.toEquiv y) * L.matrix := by
    rw [hessMatrix, hessMatrix, LorentzMap.matrix, ← LinearMap.toMatrix₂_compl₁₂]
    congr 1
    refine LinearMap.ext fun u => LinearMap.ext fun w => ?_
    simp only [hessBilin_apply, LinearMap.compl₁₂_apply]
    exact fderiv_fderiv_comp_clm hh2 (L.toEquiv : Point →L[ℝ] Point) y u w
  rw [wave_eq_trace hL2, Function.comp_apply, wave_eq_trace hh2, hH]
  congr 1
  set D := Matrix.diagonal etaSign
  set H := hessMatrix h (L.toEquiv y)
  rw [show D * (L.matrixᵀ * H * L.matrix) = (D * L.matrixᵀ * H) * L.matrix by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
    show L.matrix * (D * L.matrixᵀ * H) = (L.matrix * D * L.matrixᵀ) * H by
      simp only [Matrix.mul_assoc], L.matrix_mul_transpose]

/-- Translations commute with `□`. -/
theorem wave_comp_add_right {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) (a : Point) :
    wave (fun q => h (q + a)) = fun q => wave h (q + a) := by
  have := wave_comp_affine (hh.of_le (by norm_cast)) a (σ := 1) (by norm_num)
    (LinearIsometryEquiv.refl ℝ Space)
  have e : ∀ q : Point, a + (1 * q.1, (LinearIsometryEquiv.refl ℝ Space) q.2) = q + a := by
    intro q
    rw [add_comm]
    simp
  simp only [e] at this
  exact this

/-! ### The orthochronous Lorentz and Poincaré groups -/

namespace LorentzMap

instance : Mul LorentzMap where
  mul L L' := ⟨L'.toEquiv.trans L.toEquiv, fun u w => by simp [L.eta_map, L'.eta_map],
    (L.isFutureUnit_map (L'.isFutureUnit_map isFutureUnit_timeDir)).1⟩

instance : One LorentzMap where
  one := ⟨ContinuousLinearEquiv.refl ℝ Point, fun _ _ => rfl, by simp [timeDir]⟩

instance : Inv LorentzMap where
  inv L := ⟨L.toEquiv.symm, L.eta_symm_map, by rw [L.fst_symm_timeDir]; exact L.orthochronous⟩

@[simp] theorem mul_apply (L L' : LorentzMap) (x : Point) :
    (L * L').toEquiv x = L.toEquiv (L'.toEquiv x) := rfl

@[simp] theorem one_apply (x : Point) : (1 : LorentzMap).toEquiv x = x := rfl

@[simp] theorem inv_apply (L : LorentzMap) (x : Point) : L⁻¹.toEquiv x = L.toEquiv.symm x := rfl

/-- G4, Definition 10: the orthochronous Lorentz maps form a group. -/
instance : Group LorentzMap where
  mul_assoc _ _ _ := LorentzMap.ext (ContinuousLinearEquiv.ext (funext fun _ => rfl))
  one_mul _ := LorentzMap.ext (ContinuousLinearEquiv.ext (funext fun _ => rfl))
  mul_one _ := LorentzMap.ext (ContinuousLinearEquiv.ext (funext fun _ => rfl))
  inv_mul_cancel L := LorentzMap.ext (ContinuousLinearEquiv.ext (funext fun x => by
    change L.toEquiv.symm (L.toEquiv x) = x
    simp))

theorem timeFun_map (L : LorentzMap) (n x : Point) :
    timeFun (L.toEquiv n) (L.toEquiv x) = timeFun n x := by
  rw [timeFun, timeFun, L.eta_map]

end LorentzMap

/-- G4, Definition 10: an orthochronous Poincaré map `p ↦ L p + a`. -/
@[ext]
structure Poincare where
  L : LorentzMap
  a : Point

namespace Poincare

/-- The map `p ↦ L p + a`. -/
def toFun (g : Poincare) (p : Point) : Point := g.L.toEquiv p + g.a

instance : Mul Poincare := ⟨fun g g' => ⟨g.L * g'.L, g.L.toEquiv g'.a + g.a⟩⟩
instance : One Poincare := ⟨⟨1, 0⟩⟩
instance : Inv Poincare := ⟨fun g => ⟨g.L⁻¹, -g.L.toEquiv.symm g.a⟩⟩

@[simp] theorem mul_L (g g' : Poincare) : (g * g').L = g.L * g'.L := rfl
@[simp] theorem mul_a (g g' : Poincare) : (g * g').a = g.L.toEquiv g'.a + g.a := rfl
@[simp] theorem one_L : (1 : Poincare).L = 1 := rfl
@[simp] theorem one_a : (1 : Poincare).a = 0 := rfl
@[simp] theorem inv_L (g : Poincare) : g⁻¹.L = g.L⁻¹ := rfl
@[simp] theorem inv_a (g : Poincare) : g⁻¹.a = -g.L.toEquiv.symm g.a := rfl

/-- G4, Definition 10: the orthochronous Poincaré group. -/
instance : Group Poincare where
  mul_assoc g g' g'' := Poincare.ext (mul_assoc _ _ _) (by simp [map_add, add_assoc])
  one_mul g := Poincare.ext (one_mul _) (by simp)
  mul_one g := Poincare.ext (mul_one _) (by simp)
  inv_mul_cancel g := Poincare.ext (inv_mul_cancel _) (by simp)

theorem toFun_mul (g g' : Poincare) (p : Point) : (g * g').toFun p = g.toFun (g'.toFun p) := by
  simp [toFun, map_add, add_assoc]

theorem toFun_one (p : Point) : (1 : Poincare).toFun p = p := by
  simp [toFun]

/-- `g` as a homeomorphism of `ℝ⁴`. -/
noncomputable def toHomeomorph (g : Poincare) : Point ≃ₜ Point :=
  g.L.toEquiv.toHomeomorph.trans (Homeomorph.addRight g.a)

@[simp] theorem toHomeomorph_apply (g : Poincare) (p : Point) : g.toHomeomorph p = g.toFun p :=
  rfl

theorem toHomeomorph_symm_apply (g : Poincare) (q : Point) :
    g.toHomeomorph.symm q = g⁻¹.toFun q := by
  rw [Homeomorph.symm_apply_eq, toHomeomorph_apply]
  simp [toFun, map_add, map_neg]

theorem contDiff_toFun (g : Poincare) : ContDiff ℝ ∞ g.toFun :=
  g.L.toEquiv.contDiff.add contDiff_const

/-- G4, Lemma 11(b): `p ≤ q` iff `g p ≤ g q`. -/
theorem causalLE_iff (g : Poincare) (p q : Point) :
    causalLE (g.toFun p) (g.toFun q) ↔ causalLE p q := by
  have e : ∀ x y : Point, causalLE x y ↔ ‖(y - x).2‖ ≤ (y - x).1 := fun _ _ => Iff.rfl
  have hd : g.toFun q - g.toFun p = g.L.toEquiv (q - p) := by
    simp [toFun, map_sub]
  rw [e, e, hd]
  constructor
  · intro h
    have := (g.L⁻¹).futureCausal_map h
    simpa using this
  · exact g.L.futureCausal_map

/-- G4, Lemma 11(b) for vectors: `v` is future causal iff `L v` is (carried stage-G finding 16). -/
theorem _root_.LinearAQFT.Minkowski.LorentzMap.futureCausal_map_iff (L : LorentzMap) (v : Point) :
    ‖(L.toEquiv v).2‖ ≤ (L.toEquiv v).1 ↔ ‖v.2‖ ≤ v.1 := by
  constructor
  · intro h
    have := (L⁻¹).futureCausal_map h
    simpa using this
  · exact L.futureCausal_map

/-- G4, Lemma 11(d): `g` preserves the measure of the pairing. -/
theorem measurePreserving (g : Poincare) : MeasurePreserving g.toFun :=
  (measurePreserving_add_right volume g.a).comp g.L.measurePreserving

/-- G4, Lemma 11(e): `□(h ∘ g) = (□h) ∘ g`. -/
theorem wave_comp {h : Point → ℝ} (hh : ContDiff ℝ ∞ h) (g : Poincare) :
    wave (h ∘ g.toFun) = wave h ∘ g.toFun := by
  have e : h ∘ g.toFun = (fun q => h (q + g.a)) ∘ g.L.toEquiv := rfl
  have h1 : ContDiff ℝ ∞ (fun q => h (q + g.a)) := hh.comp (contDiff_id.add contDiff_const)
  rw [e, wave_comp_lorentz h1 g.L, wave_comp_add_right hh]
  rfl

end Poincare

/-! ### Poincaré maps as symmetries of the Green data -/

namespace Poincare

/-- G4, Proposition 12: the image of a cutoff, `(Ln, t₁ + τ_{Ln}(a), t₂ + τ_{Ln}(a))`. -/
noncomputable def mapCutoff (g : Poincare) (c : Cutoff) : Cutoff where
  n := g.L.toEquiv c.n
  hn := g.L.isFutureUnit_map c.hn
  t₁ := c.t₁ + timeFun (g.L.toEquiv c.n) g.a
  t₂ := c.t₂ + timeFun (g.L.toEquiv c.n) g.a
  lt := by linarith [c.lt]

theorem mapCutoff_mul (g g' : Poincare) (c : Cutoff) :
    (g * g').mapCutoff c = g.mapCutoff (g'.mapCutoff c) := by
  refine Cutoff.ext rfl ?_ ?_ <;>
  · simp only [mapCutoff, mul_L, mul_a, LorentzMap.mul_apply, timeFun_add,
      LorentzMap.timeFun_map]
    ring

theorem mapCutoff_one (c : Cutoff) : (1 : Poincare).mapCutoff c = c :=
  Cutoff.ext rfl (by simp [mapCutoff, timeFun_apply]) (by simp [mapCutoff, timeFun_apply])

/-- The bijection of cutoffs. -/
noncomputable def cutoffEquiv (g : Poincare) : Cutoff ≃ Cutoff where
  toFun := g.mapCutoff
  invFun := g⁻¹.mapCutoff
  left_inv c := by rw [← mapCutoff_mul, inv_mul_cancel, mapCutoff_one]
  right_inv c := by rw [← mapCutoff_mul, mul_inv_cancel, mapCutoff_one]

theorem slab_mapCutoff (g : Poincare) (c : Cutoff) :
    slab (g.mapCutoff c) = g.toHomeomorph '' slab c := by
  rw [g.toHomeomorph.image_eq_preimage_symm]
  ext q
  simp only [Set.mem_preimage, slab, Set.mem_ofPred_eq, toHomeomorph_symm_apply, toFun, inv_L,
    inv_a, LorentzMap.inv_apply, mapCutoff]
  rw [← map_neg, ← map_add, LorentzMap.timeFun_symm, timeFun_add, timeFun_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Composition with `g⁻¹` on test functions. -/
noncomputable def pushD (g : Poincare) : TestFun ≃ₗ[ℝ] TestFun where
  toFun f := ⟨f ∘ g.toHomeomorph.symm, f.contDiff.comp (by
      rw [show (g.toHomeomorph.symm : Point → Point) = g⁻¹.toFun from
        funext g.toHomeomorph_symm_apply]
      exact g⁻¹.contDiff_toFun),
    f.hasCompactSupport.comp_homeomorph _, by simp⟩
  invFun f := ⟨f ∘ g.toHomeomorph, f.contDiff.comp g.contDiff_toFun,
    f.hasCompactSupport.comp_homeomorph _, by simp⟩
  map_add' f f' := TestFunction.ext fun _ => rfl
  map_smul' c f := TestFunction.ext fun _ => rfl
  left_inv f := TestFunction.ext fun p => by
    change f (g.toHomeomorph.symm (g.toHomeomorph p)) = f p
    rw [Homeomorph.symm_apply_apply]
  right_inv f := TestFunction.ext fun p => by
    change f (g.toHomeomorph (g.toHomeomorph.symm p)) = f p
    rw [Homeomorph.apply_symm_apply]

@[simp] theorem pushD_apply (g : Poincare) (f : TestFun) (p : Point) :
    g.pushD f p = f (g.toHomeomorph.symm p) := rfl

/-- Composition with `g⁻¹` on smooth functions. -/
noncomputable def pushF (g : Poincare) : Fn ≃ₗ[ℝ] Fn where
  toFun h := ⟨(h : Point → ℝ) ∘ g.toHomeomorph.symm, (Fn.contDiff h).comp (by
      rw [show (g.toHomeomorph.symm : Point → Point) = g⁻¹.toFun from
        funext g.toHomeomorph_symm_apply]
      exact g⁻¹.contDiff_toFun)⟩
  invFun h := ⟨(h : Point → ℝ) ∘ g.toHomeomorph, (Fn.contDiff h).comp g.contDiff_toFun⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv h := Subtype.ext (funext fun p => by
    change (h : Point → ℝ) (g.toHomeomorph.symm (g.toHomeomorph p)) = (h : Point → ℝ) p
    rw [Homeomorph.symm_apply_apply])
  right_inv h := Subtype.ext (funext fun p => by
    change (h : Point → ℝ) (g.toHomeomorph (g.toHomeomorph.symm p)) = (h : Point → ℝ) p
    rw [Homeomorph.apply_symm_apply])

@[simp] theorem pushF_apply (g : Poincare) (h : Fn) (p : Point) :
    (g.pushF h : Point → ℝ) p = (h : Point → ℝ) (g.toHomeomorph.symm p) := rfl

theorem waveF_pushF (g : Poincare) (h : Fn) : waveF (g.pushF h) = g.pushF (waveF h) := by
  apply Subtype.ext
  change wave ((h : Point → ℝ) ∘ g.toHomeomorph.symm) = wave (h : Point → ℝ) ∘ g.toHomeomorph.symm
  rw [show (g.toHomeomorph.symm : Point → Point) = g⁻¹.toFun from
    funext g.toHomeomorph_symm_apply]
  exact g⁻¹.wave_comp (Fn.contDiff h)

theorem supp_pushF (g : Poincare) (h : Fn) : supp (g.pushF h) = g.toHomeomorph '' supp h := by
  rw [g.toHomeomorph.image_eq_preimage_symm]
  change closure (Function.support ((h : Point → ℝ) ∘ g.toHomeomorph.symm)) =
    g.toHomeomorph.symm ⁻¹' closure (Function.support (h : Point → ℝ))
  rw [Homeomorph.preimage_closure]
  rfl

theorem pushD_symm_apply (g : Poincare) (f : TestFun) (p : Point) :
    g.pushD.symm f p = f (g.toHomeomorph p) := rfl

theorem supp_incl_pushD_symm (g : Poincare) (f : TestFun) :
    supp (incl (g.pushD.symm f)) = g.toHomeomorph ⁻¹' supp (incl f) := by
  change closure (Function.support ((f : Point → ℝ) ∘ g.toHomeomorph)) =
    g.toHomeomorph ⁻¹' closure (Function.support (f : Point → ℝ))
  rw [Homeomorph.preimage_closure]
  rfl

theorem pairing_push (g : Poincare) (f : TestFun) (h : Fn) :
    pairing (g.pushD f) (g.pushF h) = pairing f h := by
  rw [pairing_apply, pairing_apply]
  have hmp : MeasurePreserving (g.toHomeomorph.symm : Point → Point) := by
    rw [show (g.toHomeomorph.symm : Point → Point) = g⁻¹.toFun from
      funext g.toHomeomorph_symm_apply]
    exact g⁻¹.measurePreserving
  exact hmp.integral_comp g.toHomeomorph.symm.measurableEmbedding
    (fun p => f p * (h : Point → ℝ) p)

theorem pushD_mul (g g' : Poincare) (f : TestFun) :
    (g * g').pushD f = g.pushD (g'.pushD f) := by
  refine TestFunction.ext fun p => ?_
  simp only [pushD_apply, toHomeomorph_symm_apply, mul_inv_rev, toFun_mul]

theorem pushD_one (f : TestFun) : (1 : Poincare).pushD f = f :=
  TestFunction.ext fun p => by simp [toHomeomorph_symm_apply, toFun_one]

end Poincare

end LinearAQFT.Minkowski
