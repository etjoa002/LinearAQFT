/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

/-!
# Line derivatives of real functions on a normed space

General facts used by the Minkowski instance (stages G and H), collected here in stage H,
milestone H1 (carried stage-G finding 9) from `Minkowski/Radial.lean` and
`Minkowski/Rotation.lean`: smoothness and supports of line derivatives, and second line
derivatives through the second Fréchet derivative, which commute for `C²` functions. Candidates
for Mathlib.
-/

namespace LinearAQFT

open scoped ContDiff Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineDeriv_eq_fderiv_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
    (fun z => lineDeriv ℝ f z v) = fun z => fderiv ℝ f z v :=
  funext fun z => ((hf.differentiable (by norm_num)) z).lineDeriv_eq_fderiv

theorem contDiff_lineDeriv {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun z => lineDeriv ℝ f z v) := by
  rw [lineDeriv_eq_fderiv_of_contDiff (hf.of_le (by exact_mod_cast le_top)) v]
  refine contDiff_infty.2 fun n => ?_
  exact ((hf.of_le (by exact_mod_cast le_top) : ContDiff ℝ (n + 1) f).fderiv_right le_rfl).clm_apply
    contDiff_const

theorem tsupport_lineDeriv_subset (f : E → ℝ) (v : E) :
    tsupport (fun z => lineDeriv ℝ f z v) ⊆ tsupport f := by
  refine closure_minimal (fun q hq => ?_) (isClosed_tsupport f)
  by_contra hn
  apply hq
  have heq : f =ᶠ[𝓝 q] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.1 hn
  have hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) q :=
    (hasFDerivAt_const (0 : ℝ) q).congr_of_eventuallyEq heq
  simpa using (hd.hasLineDerivAt v).lineDeriv

/-- Mixed second line derivatives through the second derivative. -/
theorem lineDeriv_lineDeriv_eq_fderiv {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z v w : E) :
    lineDeriv ℝ (fun z => lineDeriv ℝ f z v) z w = fderiv ℝ (fderiv ℝ f) z w v := by
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd3 : Differentiable ℝ (fun z => fderiv ℝ f z v) := fun z => (hd2 z).clm_apply
    (differentiableAt_const v)
  rw [lineDeriv_eq_fderiv_of_contDiff (hf.of_le (by norm_num)) v, (hd3 z).lineDeriv_eq_fderiv,
    fderiv_clm_apply (hd2 z) (differentiableAt_const v)]
  simp

/-- Mixed line derivatives of a `C²` function commute. -/
theorem lineDeriv_lineDeriv_comm {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z v w : E) :
    lineDeriv ℝ (fun z => lineDeriv ℝ f z v) z w =
      lineDeriv ℝ (fun z => lineDeriv ℝ f z w) z v := by
  rw [lineDeriv_lineDeriv_eq_fderiv hf, lineDeriv_lineDeriv_eq_fderiv hf]
  exact (ContDiffAt.isSymmSndFDerivAt (ContDiff.contDiffAt hf) (by simp)) w v

/-- The second line derivative is the second derivative of the restriction to the line. -/
theorem lineDeriv_lineDeriv_eq (f : E → ℝ) (x v : E) :
    lineDeriv ℝ (fun z => lineDeriv ℝ f z v) x v =
      deriv (deriv fun s : ℝ => f (x + s • v)) 0 := by
  have h : ∀ s : ℝ, lineDeriv ℝ f (x + s • v) v = deriv (fun s : ℝ => f (x + s • v)) s := by
    intro s
    have e : (fun u : ℝ => f (x + s • v + u • v)) = fun u => f (x + (s + u) • v) := by
      funext u
      rw [add_smul, add_assoc]
    change deriv (fun u : ℝ => f (x + s • v + u • v)) 0 = _
    rw [e, deriv_comp_const_add (f := fun s : ℝ => f (x + s • v)), add_zero]
  change deriv (fun s : ℝ => lineDeriv ℝ f (x + s • v) v) 0 = _
  simp_rw [h]

/-- For a `C²` function the second line derivative is the second derivative on the diagonal. -/
theorem lineDeriv_lineDeriv_eq_iteratedFDeriv {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    lineDeriv ℝ (fun z => lineDeriv ℝ f z v) x v = iteratedFDeriv ℝ 2 f x ![v, v] := by
  rw [lineDeriv_lineDeriv_eq_fderiv hf, iteratedFDeriv_two_apply]
  simp

/-- Rescaling the line: `(d/ds)² g(c s) = c² g''`. -/
theorem deriv_deriv_comp_mul (g : ℝ → ℝ) (c : ℝ) :
    deriv (deriv fun s : ℝ => g (c * s)) 0 = c ^ 2 * deriv (deriv g) 0 := by
  have h1 : (deriv fun s : ℝ => g (c * s)) = fun s => c * deriv g (c * s) := by
    funext s
    rw [deriv_comp_mul_left (f := g), smul_eq_mul]
  rw [h1, deriv_const_mul_field, deriv_comp_mul_left (f := deriv g), smul_eq_mul, mul_zero]
  ring

end LinearAQFT
