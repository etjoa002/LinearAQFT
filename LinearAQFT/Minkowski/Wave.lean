/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Minkowski.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# The wave operator along lines, and its invariance

Stage G, milestone G3 (moved from `Rotation.lean` on 30 Sep 2026, so that `Lorentz.lean` does
not depend on the rotation average). `□` by second derivatives along the coordinate lines; the
spatial part does not depend on the orthonormal basis; `□` commutes with the maps
`q ↦ b + (σ q⁰, L q⃗)` for `σ = ±1` and `L` a linear isometry of space.

## Main results

* `wave_apply_eq_deriv`, `sum_deriv_deriv_orthonormalBasis`.
* `wave_comp_affine`: `□(h ∘ M) = (□h) ∘ M` (used for G3, Lemma 9, Proposition 4(b), and G4).
-/

namespace LinearAQFT.Minkowski

open scoped ContDiff Topology InnerProductSpace
open MeasureTheory Set Filter Function

/-! ### `□` along lines, and its invariance -/

/-- `□` by second derivatives along the coordinate lines. -/
theorem wave_apply_eq_deriv (h : Point → ℝ) (q : Point) :
    wave h q = deriv (deriv fun s : ℝ => h (q + s • timeDir)) 0 -
      ∑ i, deriv (deriv fun s : ℝ => h (q + s • spaceDir i)) 0 := by
  simp only [wave, Pi.sub_apply, Finset.sum_apply]
  change lineDeriv ℝ (fun z => lineDeriv ℝ h z timeDir) q timeDir -
      ∑ i, lineDeriv ℝ (fun z => lineDeriv ℝ h z (spaceDir i)) q (spaceDir i) = _
  simp only [lineDeriv_lineDeriv_eq]

/-- The spatial part of `□` does not depend on the orthonormal basis. -/
theorem sum_deriv_deriv_orthonormalBasis {h : Point → ℝ} (hh : ContDiff ℝ 2 h) (p : Point)
    (u : OrthonormalBasis (Fin 3) ℝ Space) :
    ∑ i, deriv (deriv fun s : ℝ => h (p + s • ((0 : ℝ), u i))) 0 =
      ∑ i, deriv (deriv fun s : ℝ => h (p + s • spaceDir i)) 0 := by
  set φ : Space → ℝ := fun y => h (p.1, y)
  have hφ : ContDiff ℝ 2 φ := hh.comp (contDiff_const.prodMk contDiff_id)
  have key : ∀ w : Space, deriv (deriv fun s : ℝ => h (p + s • ((0 : ℝ), w))) 0 =
      iteratedFDeriv ℝ 2 φ p.2 ![w, w] := by
    intro w
    have e : (fun s : ℝ => h (p + s • ((0 : ℝ), w))) = fun s : ℝ => φ (p.2 + s • w) := by
      funext s
      simp only [φ, Prod.smul_mk, smul_zero]
      congr 1
      ext <;> simp
    rw [e, ← lineDeriv_lineDeriv_eq, lineDeriv_lineDeriv_eq_iteratedFDeriv hφ]
  have hs : ∀ i, spaceDir i = ((0 : ℝ), EuclideanSpace.basisFun (Fin 3) ℝ i) := by
    intro i
    rw [EuclideanSpace.basisFun_apply]
    rfl
  simp only [hs, key]
  have h1 := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f := φ) u) p.2
  have h2 := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f := φ) (EuclideanSpace.basisFun (Fin 3) ℝ)) p.2
  exact h1.symm.trans h2

/-- `□(h ∘ M) = (□h) ∘ M` for `M q = b + (σ q⁰, L q⃗)`, `σ² = 1`, `L` a linear isometry. -/
theorem wave_comp_affine {h : Point → ℝ} (hh : ContDiff ℝ 2 h) (b : Point) {σ : ℝ}
    (hσ : σ ^ 2 = 1) (L : Space ≃ₗᵢ[ℝ] Space) :
    wave (fun q : Point => h (b + (σ * q.1, L q.2))) =
      fun q : Point => wave h (b + (σ * q.1, L q.2)) := by
  funext q
  set M : Point := b + (σ * q.1, L q.2)
  have hline : ∀ (v : Point) (s : ℝ),
      b + (σ * (q + s • v).1, L (q + s • v).2) = M + s • (σ * v.1, L v.2) := by
    intro v s
    simp only [M, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, map_add, map_smul,
      Prod.smul_mk, smul_eq_mul]
    ext <;> simp <;> ring
  rw [wave_apply_eq_deriv, wave_apply_eq_deriv]
  simp only [hline]
  congr 1
  · have e : (fun s : ℝ => h (M + s • (σ * timeDir.1, L timeDir.2))) =
        fun s => (fun s : ℝ => h (M + s • timeDir)) (σ * s) := by
      funext s
      congr 1
      simp [timeDir, Prod.smul_mk, mul_comm]
    rw [e, deriv_deriv_comp_mul (fun s : ℝ => h (M + s • timeDir)) σ, hσ, one_mul]
  · have e : ∀ i, (σ * (spaceDir i).1, L (spaceDir i).2) =
        ((0 : ℝ), (EuclideanSpace.basisFun (Fin 3) ℝ).map L i) := by
      intro i
      simp [spaceDir, EuclideanSpace.basisFun_apply]
    simp only [e]
    exact sum_deriv_deriv_orthonormalBasis hh M _

end LinearAQFT.Minkowski
