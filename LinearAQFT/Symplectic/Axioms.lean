/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Symplectic.Net
import BosonicLean.Weyl.Primitive

/-!
# The main theorem of [Dimock] for phase-space data

Milestone D1, item 6. For phase-space data with a nondegenerate form, the CCR net is generating,
its algebra is primitive (given an irreducible representation), and it is causal and has the
time-slice property: Axioms 1-4 of [Dimock], Theorem 4. Axiom 5 is
`ccrNet_isCovariancePair` (milestone C), which is a statement about every isomorphism of
phase-space data and is kept separate.

## Main results

* `LinearAQFT.Symplectic.ccrNet_axioms_primitive`.
-/

namespace LinearAQFT.Symplectic

open Net BosonicLean.Weyl

variable {R : Type*} [Preorder R] {C : CausalIndex R}
variable {D V : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V]

/-- D1, Theorem 17 (Theorem 4 of [Dimock], Axioms 1-4): for phase-space data with a
nondegenerate form and an irreducible representation of its CCR algebra, the CCR net is
generating, primitive, causal and has the time-slice property. -/
theorem ccrNet_axioms_primitive (Φ : PhaseSpace C D V) (hnd : Φ.sigma.SeparatingLeft)
    (h : BosonicLean.HasIrreducibleRep (CCR Φ.sigma)) :
    (ccrNet Φ).IsGenerating ∧ BosonicLean.IsPrimitive (CCR Φ.sigma) ∧ IsCausal C (ccrNet Φ) ∧
      HasTimeSlice C (ccrNet Φ) :=
  ⟨weylNet_isGenerating _ _, BosonicLean.Weyl.CCR.isPrimitive Φ.isAlt hnd h, weylNet_isCausal _ _,
    weylNet_hasTimeSlice _ _⟩

/-- Generation, causality and the time-slice property of the CCR net hold for all phase-space
data, with no hypothesis; only primitivity in `ccrNet_axioms_primitive` needs an irreducible
representation. -/
theorem ccrNet_axioms (Φ : PhaseSpace C D V) :
    (ccrNet Φ).IsGenerating ∧ IsCausal C (ccrNet Φ) ∧ HasTimeSlice C (ccrNet Φ) :=
  ⟨weylNet_isGenerating _ _, weylNet_isCausal _ _, weylNet_hasTimeSlice _ _⟩

end LinearAQFT.Symplectic
