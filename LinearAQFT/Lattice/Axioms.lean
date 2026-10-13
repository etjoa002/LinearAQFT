/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Lattice.Net
import LinearAQFT.Symplectic.Axioms

/-!
# The main theorem of [Dimock] on the lattice

Milestone D1, item 6. The CCR algebra of the lattice field is simple for every `m²`, with no
hypotheses. Given an irreducible representation, the lattice CCR net satisfies Axioms 1–4 of
[Dimock] and covariance under the translations of `ℤ²` (Axiom 5 for the translation group).

## Main results

* `LinearAQFT.Lattice.ccr_isSimpleRing`, `LinearAQFT.Lattice.ccrNet_axioms_primitive`.
-/

namespace LinearAQFT.Lattice

open Symplectic BosonicLean.Weyl Net

variable (m2 : ℝ)

/-- D1, Corollary 18: the CCR algebra of the lattice field is simple, with no hypotheses. -/
theorem ccr_isSimpleRing : IsSimpleRing (CCR (phaseSpace m2).sigma) :=
  CCR.isSimpleRing (phaseSpace m2).isAlt fun u h => phaseSpace_sigma_nondegenerate m2 u h

/-- D1, Corollary 18: given an irreducible representation of its CCR algebra, the CCR net of
the lattice field satisfies Axioms 1–4 of [Dimock] and covariance under the translations of
`ℤ²`: it is generating, primitive, causal, has the time-slice property, and is translation
covariant. -/
theorem ccrNet_axioms_primitive (h : BosonicLean.HasIrreducibleRep (CCR (phaseSpace m2).sigma)) :
    (ccrNet (phaseSpace m2)).IsGenerating ∧ BosonicLean.IsPrimitive (CCR (phaseSpace m2).sigma) ∧
      IsCausal causalIndex (ccrNet (phaseSpace m2)) ∧
      HasTimeSlice causalIndex (ccrNet (phaseSpace m2)) ∧
      IsCovariantUnder (ccrNet (phaseSpace m2)) translateHom (ccrTranslate m2) :=
  have h4 := Symplectic.ccrNet_axioms_primitive (phaseSpace m2)
    (fun u hu => phaseSpace_sigma_nondegenerate m2 u hu) h
  ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2, (ccrNet_phaseSpace m2).2.2.2⟩

end LinearAQFT.Lattice
