/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Unit vectors in normed spaces

A general fact used by the positivity argument of stage H (milestone H4, Proposition 8), moved here
from `Minkowski/Huygens.lean` at the stage-H closeout (carried H4 finding 1) under the placement
rule: in a nontrivial real normed space every vector is `‖d‖ • u` for a unit vector `u`. Namespace
`LinearAQFT`.
-/

namespace LinearAQFT

/-- Every vector `d` of a nontrivial real normed space is `‖d‖ • u` for a unit vector `u`. -/
theorem exists_unit_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (d : E) : ∃ u : E, ‖u‖ = 1 ∧ d = ‖d‖ • u := by
  by_cases hd : d = 0
  · obtain ⟨u, hu⟩ := exists_norm_eq E zero_le_one
    exact ⟨u, hu, by simp [hd]⟩
  · refine ⟨‖d‖⁻¹ • d, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hd)]
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hd), one_smul]

end LinearAQFT
