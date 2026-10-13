import LinearAQFT.Lattice.Axioms

/-!
# Dimock slice: the lattice instance

Facade for the slice `slices/dimock-lattice.toml`: the unconditional lattice instance on `ℤ²`,
restated from the statement probe of milestone D1 (Corollary 18). It adds no declarations.
-/

open LinearAQFT LinearAQFT.Net LinearAQFT.Symplectic
open BosonicLean BosonicLean.Weyl

-- D1, Corollary 18: simplicity with no hypothesis, and Axioms 1–5 with translation covariance.
example (m2 : ℝ) : IsSimpleRing (CCR (Lattice.phaseSpace m2).sigma) :=
  Lattice.ccr_isSimpleRing m2
example (m2 : ℝ) (h : HasIrreducibleRep (CCR (Lattice.phaseSpace m2).sigma)) :
    (ccrNet (Lattice.phaseSpace m2)).IsGenerating ∧
      IsPrimitive (CCR (Lattice.phaseSpace m2).sigma) ∧
      IsCausal Lattice.causalIndex (ccrNet (Lattice.phaseSpace m2)) ∧
      HasTimeSlice Lattice.causalIndex (ccrNet (Lattice.phaseSpace m2)) ∧
      IsCovariantUnder (ccrNet (Lattice.phaseSpace m2)) Lattice.translateHom
        (Lattice.ccrTranslate m2) :=
  Lattice.ccrNet_axioms_primitive m2 h

#print axioms LinearAQFT.Lattice.ccr_isSimpleRing
#print axioms LinearAQFT.Lattice.ccrNet_axioms_primitive
