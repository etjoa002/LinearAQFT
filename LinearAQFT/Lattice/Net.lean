/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Lattice.PhaseSpace
import LinearAQFT.Symplectic.Net

/-!
# The net of the lattice field

The CCR net of the lattice phase-space data satisfies generation, causality and time slice,
and is covariant under the translation group `ℤ²`, for every `m²` and with no hypotheses.

## Main definitions

* `ccrTranslate`: the group homomorphism `a ↦ α_{θ_a}` (E2, Theorem 7).

## Main statements

* `ccrNet_phaseSpace` (E2, Theorem 7).
-/

noncomputable section

namespace LinearAQFT

open Symplectic BosonicLean.Weyl Net

namespace Lattice

variable (m2 : ℝ)

/-- E2, Theorem 7: `a ↦ α_{θ_a}`, a group homomorphism from the translations into the
automorphisms of the CCR algebra. -/
def ccrTranslate :
    Multiplicative Point →* (CCR (phaseSpace m2).sigma ≃⋆ₐ[ℂ] CCR (phaseSpace m2).sigma) :=
  ccrAlphaHom (fun a => translateIso m2 a.toAdd) (translateIso_T_zero m2)
    fun a b => translateIso_T_add m2 a.toAdd b.toAdd

@[simp] theorem ccrTranslate_apply (a : Multiplicative Point) :
    ccrTranslate m2 a = ccrAlpha (translateIso m2 a.toAdd) := rfl

/-- E2, Theorem 7: the CCR net of the lattice field is generating, causal, has the
time-slice property and is covariant under the translations, with no hypotheses. -/
theorem ccrNet_phaseSpace :
    (ccrNet (phaseSpace m2)).IsGenerating ∧ IsCausal causalIndex (ccrNet (phaseSpace m2)) ∧
      HasTimeSlice causalIndex (ccrNet (phaseSpace m2)) ∧
      IsCovariantUnder (ccrNet (phaseSpace m2)) translateHom (ccrTranslate m2) :=
  ⟨weylNet_isGenerating _ _, weylNet_isCausal _ _, weylNet_hasTimeSlice _ _,
    ccrNet_isCovariantUnder _ _ _ translateHom fun _ => rfl⟩

end Lattice

end LinearAQFT

end
