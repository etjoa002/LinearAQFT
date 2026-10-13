import LinearAQFT.Minkowski.Poincare

/-!
# Dimock slice: Green data and the massless field on Minkowski space

Facade for the slice `slices/dimock-minkowski.toml`, restated from the statement probes of
stage F (Theorem 9) and milestone G4 (Corollary 8, Theorem 13). It adds no declarations. The
time-slice axiom here is the pointwise form with inertial slabs (notes Remark 8.13).
-/

open LinearAQFT LinearAQFT.Green LinearAQFT.Net LinearAQFT.Symplectic
open LinearAQFT.Minkowski
open BosonicLean BosonicLean.Weyl

noncomputable section

section General

variable {X D F : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup F] [Module ℝ F]
variable (G : GreenData X D F)

-- F, Theorem 9: Axioms 1–4 for the CCR net of any Green data.
example (h : HasIrreducibleRep (CCR G.phaseSpace.sigma)) :
    (ccrNet G.phaseSpace).IsGenerating ∧ IsPrimitive (CCR G.phaseSpace.sigma) ∧
      IsCausal G.causalIndex (ccrNet G.phaseSpace) ∧
      HasTimeSlice G.causalIndex (ccrNet G.phaseSpace) :=
  G.ccrNet_axioms_primitive h

end General

-- G4, Corollary 8: Axioms 1–4 for the free massless field on 3+1 Minkowski space.
example (h : HasIrreducibleRep (CCR greenData.phaseSpace.sigma)) :
    (Symplectic.ccrNet greenData.phaseSpace).IsGenerating ∧
      IsPrimitive (CCR greenData.phaseSpace.sigma) ∧
      IsCausal greenData.causalIndex (Symplectic.ccrNet greenData.phaseSpace) ∧
      HasTimeSlice greenData.causalIndex (Symplectic.ccrNet greenData.phaseSpace) :=
  Minkowski.ccrNet_axioms_primitive h

-- G4, Theorem 13: covariance under the orthochronous Poincaré group (Axiom 5).
example :
    IsCovariantUnder (Symplectic.ccrNet greenData.phaseSpace) poincareKappa poincareAlpha :=
  isCovariantUnder_poincare

end

#print axioms LinearAQFT.Green.GreenData.ccrNet_axioms_primitive
#print axioms LinearAQFT.Minkowski.ccrNet_axioms_primitive
#print axioms LinearAQFT.Minkowski.isCovariantUnder_poincare
